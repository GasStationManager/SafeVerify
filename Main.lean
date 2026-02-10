/-
Adapted from https://github.com/leanprover/lean4checker/blob/master/Main.lean
and
https://github.com/kim-em/lean-training-data/blob/master/scripts/declaration_types.lean
-/

import SafeVerify
import Lean
import Cli

open Lean Meta Core SafeVerify

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]

def checkAxioms (info : Info) : Bool := Id.run do
  for a in info.axioms do
    if a ∉ AllowedAxioms then return false
  return true

open Std

/-- Takes the environment obtained after replaying all the constant in a file and outputs
a hashmap storing the infos corresponding to all the theorems and definitions in the file. -/
def processFileDeclarations
    (env : Environment) : IO <| HashMap Name Info := do
  let mut out : HashMap Name Info := {}
  for (n, ci) in env.constants.map₂  do
    if ci.kind ∈ ["theorem", "def", "opaque"] then
      let (_, s) := (CollectAxioms.collect n).run env |>.run {}
      out := out.insert n ⟨n, ci, s.axioms⟩
  return out

/-- Takes two arrays of `Info` and check that the declarations match (i.e. same kind, same type, and same
value if they are definitions). -/
def checkTargets (targetInfos submissionInfos : HashMap Name Info) : (HashMap Name SafeVerifyOutcome) :=
  targetInfos.map fun _ target_info ↦ Id.run do
    let ⟨n, target_constInfo, axs⟩ := target_info
    if let some submission_info := submissionInfos.get? n then
      let submission_constInfo := submission_info.constInfo
      if target_constInfo.kind ≠ submission_constInfo.kind then
        return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := some <| .kind target_constInfo.kind submission_constInfo.kind}
      if submission_constInfo.kind == "theorem" && !equivThm target_constInfo submission_constInfo then
        return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := some .thmType}
      if submission_constInfo.kind == "def" && !equivDefn target_constInfo submission_constInfo (`sorryAx ∉ axs)  then
        return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := some .defnCheck}
      if submission_constInfo.kind == "opaque" && !equivOpaq target_constInfo submission_constInfo then
        return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := some .opaqueCheck}
      if !checkAxioms submission_info then
        return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := some .axioms}
      return {targetInfo := target_info, submissionConstant := submission_constInfo, failureMode := none}
    else
      return {targetInfo := target_info, submissionConstant := none, failureMode := some .notFound}

/-- Replays a lean file and outputs a hashmap storing the `Info`s corresponding to
the theorems and definitions in the file. -/
def replayFile (filePath : System.FilePath) (disallowPartial : Bool) : IO (HashMap Name Info) := do
  IO.println s!"Replaying {filePath}"
  unless (← filePath.pathExists) do
    throw <| IO.userError s!"object file '{filePath}' does not exist"
  let (mod, _) ← readModuleData filePath
  let env ← importModules mod.imports {} 0
  IO.println "Finished setting up the environement."
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    if ci.isUnsafe then
      throw <| IO.userError s!"unsafe constant {name} detected"
    if disallowPartial && ci.isPartial then
      throw <| IO.userError s!"partial constant {name} detected"
    newConstants := newConstants.insert name ci
  let env ← env.replay newConstants
  IO.println s!"Finished replay. Found {newConstants.size} declarations."
  unsafe processFileDeclarations env

-- TODO: implement option to store ouput as a JSON file (with outcome for each result).

/-- Print verbose information about a type mismatch between two constants. -/
def printVerboseTypeMismatch (targetConst submissionConst : ConstantInfo) : IO Unit := do
  IO.eprintln s!"  Expected type: {targetConst.type}"
  IO.eprintln s!"  Got type:      {submissionConst.type}"
  if targetConst.levelParams != submissionConst.levelParams then
    IO.eprintln s!"  Expected level params: {targetConst.levelParams}"
    IO.eprintln s!"  Got level params:      {submissionConst.levelParams}"

/-- Print verbose information about a definition mismatch. -/
def printVerboseDefnMismatch (targetConst submissionConst : ConstantInfo) : IO Unit := do
  if targetConst.type != submissionConst.type then
    IO.eprintln s!"  Type mismatch:"
    IO.eprintln s!"    Expected: {targetConst.type}"
    IO.eprintln s!"    Got:      {submissionConst.type}"
  if targetConst.levelParams != submissionConst.levelParams then
    IO.eprintln s!"  Level params mismatch:"
    IO.eprintln s!"    Expected: {targetConst.levelParams}"
    IO.eprintln s!"    Got:      {submissionConst.levelParams}"
  if let (.defnInfo tval₁, .defnInfo tval₂) := (targetConst, submissionConst) then
    if tval₁.safety != tval₂.safety then
      IO.eprintln s!"  Safety mismatch: expected {tval₁.safety}, got {tval₂.safety}"
    if tval₁.value != tval₂.value then
      IO.eprintln s!"  Value mismatch (values differ)"

/-- Print verbose information about an opaque mismatch. -/
def printVerboseOpaqueMismatch (targetConst submissionConst : ConstantInfo) : IO Unit := do
  if targetConst.type != submissionConst.type then
    IO.eprintln s!"  Type mismatch:"
    IO.eprintln s!"    Expected: {targetConst.type}"
    IO.eprintln s!"    Got:      {submissionConst.type}"
  if targetConst.levelParams != submissionConst.levelParams then
    IO.eprintln s!"  Level params mismatch:"
    IO.eprintln s!"    Expected: {targetConst.levelParams}"
    IO.eprintln s!"    Got:      {submissionConst.levelParams}"
  if let (.opaqueInfo tval₁, .opaqueInfo tval₂) := (targetConst, submissionConst) then
    if tval₁.isUnsafe != tval₂.isUnsafe then
      IO.eprintln s!"  Safety mismatch: expected isUnsafe={tval₁.isUnsafe}, got isUnsafe={tval₂.isUnsafe}"
    if tval₁.value != tval₂.value then
      IO.eprintln s!"  Value mismatch (values differ)"

/-- Run the main SafeVerify check on a pair of file (the targetFile containing statements and the
submission file containing proofs). -/
def runSafeVerify (targetFile submissionFile : System.FilePath)
    (disallowPartial : Bool) (verbose : Bool := false) : IO Unit := do
  IO.println "------------------"
  let targetInfo ← replayFile targetFile disallowPartial
  IO.println "------------------"
  let submissionInfo ← replayFile submissionFile disallowPartial
  for (n, info) in submissionInfo do
    if !checkAxioms info then
      throw <| IO.userError s!"{n} used disallowed axioms. {info.axioms}"
  let checkOutcome := checkTargets targetInfo submissionInfo
  IO.println "------------------"
  let mut hasErrors := false
  for (name, outcome) in checkOutcome do
    if let some failure := outcome.failureMode then
      hasErrors := true
      IO.eprintln s!"Found a problem in {submissionFile} with declaration {name}: {failure}"
      if verbose then
        match failure with
        | .thmType =>
          if let some submissionConst := outcome.submissionConstant then
            printVerboseTypeMismatch outcome.targetInfo.constInfo submissionConst
        | .defnCheck =>
          if let some submissionConst := outcome.submissionConstant then
            printVerboseDefnMismatch outcome.targetInfo.constInfo submissionConst
        | .opaqueCheck =>
          if let some submissionConst := outcome.submissionConstant then
            printVerboseOpaqueMismatch outcome.targetInfo.constInfo submissionConst
        | .axioms =>
          if let some submissionInfo := submissionInfo.get? name then
            IO.eprintln s!"  Disallowed axioms used: {submissionInfo.axioms.filter (· ∉ AllowedAxioms)}"
        | _ => pure ()
  IO.println "------------------"
  if hasErrors then
    throw <| IO.userError s!"SafeVerify check failed for {submissionFile}"
  IO.println s!"Finished."

open Cli

instance : ParseableType System.FilePath where
  name := "System.FilePath"
  parse? str := some { toString := str }

/--
Takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
First file (the target) may contain theorem / function signature with sorry in their bodies;
the second file is expected to fill them.
Uses Environment.replay to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.
-/
def runMain (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  IO.println s!"Currently running on Lean v{Lean.versionString}"
  let disallowPartial := p.hasFlag "disallow-partial"
  let verbose := p.hasFlag "verbose"
  let targetFile  := p.positionalArg! "target" |>.as! System.FilePath
  let submissionFile  := p.positionalArg! "submission" |>.as! System.FilePath
  IO.println s!"Running SafeVerify on target file: {targetFile} and submission file: {submissionFile}."
  runSafeVerify targetFile submissionFile disallowPartial verbose
  return 0

/-- The main CLI interface for `SafeVerify`. This will be expanded as we add more
functionalities.-/
def mainCmd : Cmd := `[Cli|
  mainCmd VIA runMain;
  "Run SafeVerify on a pair of files (TargetFile, SubmissionFile). "
  -- TODO: add flags to control which axioms and allowed and so on.
  FLAGS:
    "disallow-partial"; "Disallow partial definitions"
    v, "verbose"; "Enable verbose error messages showing detailed type information"

  ARGS:
    target : System.FilePath; "The target file"
    submission : System.FilePath; "The submission file"
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
