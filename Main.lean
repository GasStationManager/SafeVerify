/-
Adapted from https://github.com/leanprover/lean4checker/blob/master/Main.lean
and
https://github.com/kim-em/lean-training-data/blob/master/scripts/declaration_types.lean
-/

import SafeVerify
import SafeVerify.Monads
import Lean
import Cli

open Lean Meta Core SafeVerify
open Std

/-- Takes the environment obtained after replaying all the constant in a file and outputs
a hashmap storing the infos corresponding to all the theorems and definitions in the file. -/
def processFileDeclarations (env : Environment) : HashMap Name Info := Id.run do
  let mut out : HashMap Name Info := {}
  for (_, ci) in env.constants.map₂  do
    if ci.kind ∈ ["theorem", "def", "opaque"] then
      let (_, s) := (CollectAxioms.collect ci.name).run env |>.run {}
      out := out.insert ci.name ⟨ci, s.axioms⟩
  return out

/-- Check if an Info uses only allowed axioms -/
def checkAxioms (info : Info) (allowedAxioms : Array Name) : Bool := Id.run do
  for a in info.axioms do
    if a ∉ allowedAxioms then return false
  return true

/-- Determine the failure mode for a single target/submission pair.
`isDisproof` indicates whether the submission is a disproof (using the `.disproof` suffix
convention). When `isDisproof` is true, the theorem type check is negated: we verify that the
submission proves the negation of the target statement instead of the statement itself. -/
def Info.toFailureMode (target submission : Info) (isDisproof : Bool)
    (allowedAxioms : Array Name) (env : Environment) :
    IO (Option SafeVerifyOutcome) := do
  if target.constInfo.kind ≠ submission.constInfo.kind then
    return some ⟨target, submission, some <| .kind target.constInfo.kind submission.constInfo.kind⟩
  -- This is a little hacky since it would be better to avoid string matching but let's deal with that later.
  if submission.constInfo.kind == "theorem" then
    if !isDisproof then
      if !equivThm target.constInfo submission.constInfo then
        return some ⟨target, submission, some .thmType⟩
    else
      let negOk : CoreM Bool := checkNegatedTheorem target.constInfo submission.constInfo
      let negOk ← negOk.toIO' {fileName := "", fileMap := default} {env := env}
      if !negOk then
        return some ⟨target, submission, some .thmType⟩
  if submission.constInfo.kind == "def"
      && !equivDefn target.constInfo submission.constInfo (`sorryAx ∉ target.axioms) then
    return some ⟨target, submission, some .defnCheck⟩
  if submission.constInfo.kind == "opaque" && !equivOpaq target.constInfo submission.constInfo then
    return some ⟨target, submission, some .opaqueCheck⟩
  if !checkAxioms submission allowedAxioms then
    return some ⟨target, submission, some .axioms⟩
  return some ⟨target, submission, none⟩

/-- Check that the declarations match (i.e. same kind, same type, and same
value if they are definitions). Reads Settings and Decls from context, updates State with outcomes.
When `allowDisproofs` is set in Settings, also looks for `foo.disproof` submissions as valid
negation proofs of target theorem `foo`. -/
def checkTargets : SafeVerifyM Unit := do
  let settings ← getSettings
  let decls ← getDecls
  let outArray ← decls.targetDecls.toArray.mapM fun (name, targetInfo) ↦ do
    let mut optionInfo := decls.submissionDecls.get? targetInfo.constInfo.name
    let optionInfoDisproof :=
      if settings.allowDisproofs
        then decls.submissionDecls.get? <| targetInfo.constInfo.name.str "disproof"
        else none
    if optionInfoDisproof.isSome then optionInfo := optionInfoDisproof
    let optionOutcome ← optionInfo.bindM
      (Info.toFailureMode targetInfo · optionInfoDisproof.isSome settings.allowedAxioms decls.env)
    return (name, optionOutcome.getD (dflt := ⟨targetInfo, none, some .notFound⟩))
  let checkOutcome := HashMap.ofArray outArray
  modify fun s => { s with checkOutcomes := checkOutcome }

/-- Replays a lean file and outputs a hashmap storing the `Info`s corresponding to
the theorems and definitions in the file, together with the resulting environment. -/
def replayFile (filePath : System.FilePath) (disallowPartial : Bool) :
    IO (HashMap Name Info × Environment) := do
  IO.eprintln s!"Replaying {filePath}"
  unless (← filePath.pathExists) do
    throw <| IO.userError s!"object file '{filePath}' does not exist"
  let (mod, _) ← readModuleData filePath
  let env ← importModules mod.imports {} 0
  IO.eprintln "Finished setting up the environment."
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    if ci.isUnsafe then
      throw <| IO.userError s!"unsafe constant {name} detected"
    if disallowPartial && ci.isPartial then
      throw <| IO.userError s!"partial constant {name} detected"
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  IO.eprintln s!"Finished replay. Found {newConstants.size} declarations."
  return (processFileDeclarations env', env')

/-- Replays the target (challenge) file and extracts declarations plus the environment.
    Reads file path and settings from the Settings context. -/
def replayChallenges : ReaderT SafeVerify.Settings IO (HashMap Name Info × Environment) := do
  let settings ← read
  replayFile settings.targetFile settings.disallowPartial

/-- Replays the submission (solution) file and extracts declarations.
    Reads file path and settings from the Settings context. -/
def replaySolutions : ReaderT SafeVerify.Settings IO (HashMap Name Info) := do
  let settings ← read
  let (decls, _) ← replayFile settings.submissionFile settings.disallowPartial
  return decls

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
      -- TODO(Paul-Lez): currently this will never occur because we throw an error whenever we reach an unsafe constant - fix this?
      -- probably we should track dissalowed opaque (and partial) constant in a CheckFailureField.
      IO.eprintln s!"  Safety mismatch: expected isUnsafe={tval₁.isUnsafe}, got isUnsafe={tval₂.isUnsafe}"
    if tval₁.value != tval₂.value then
      IO.eprintln s!"  Value mismatch (values differ)"

/-- Run the main SafeVerify check. This uses the three-layer monadic design with Settings, Decls, and State. -/
def runSafeVerify : SafeVerifyM Unit := do
  let settings ← getSettings
  let decls ← getDecls

  IO.eprintln "------------------"
  -- Check for disallowed axioms
  for (n, info) in decls.submissionDecls do
    if !checkAxioms info settings.allowedAxioms then
      IO.eprintln s!"{n} used disallowed axioms. {info.axioms}"

  -- Run the checks and store outcomes in state
  checkTargets
  IO.eprintln "------------------"

  -- Print results
  let state ← get
  let checkOutcome := state.checkOutcomes
  let mut hasFailures := false
  for (name, outcome) in checkOutcome do
    if let some failure := outcome.failureMode then
      hasFailures := true
      IO.eprintln s!"Found a problem in {settings.submissionFile} with declaration {name}: {failure}"
      if settings.verbose then
        match failure with
        | .thmType =>
          if let some submissionConst := outcome.solutionInfo then
            printVerboseTypeMismatch outcome.targetInfo.constInfo submissionConst.constInfo
        | .defnCheck =>
          if let some submissionConst := outcome.solutionInfo then
            printVerboseDefnMismatch outcome.targetInfo.constInfo submissionConst.constInfo
        | .opaqueCheck =>
          if let some submissionConst := outcome.solutionInfo then
            printVerboseOpaqueMismatch outcome.targetInfo.constInfo submissionConst.constInfo
        | .axioms =>
          if let some info := decls.submissionDecls.get? name then
            IO.eprintln s!"  Disallowed axioms used: {info.axioms.filter (· ∉ settings.allowedAxioms)}"
        | _ => pure ()
  IO.eprintln "------------------"
  if hasFailures then
    IO.eprintln "SafeVerify check failed."
    if !settings.verbose then
      IO.eprintln s!"For more diagnostic information about failures, run safe_verify with the -v (or --verbose) flag."
  else
    IO.eprintln "SafeVerify check passed."

open Cli

instance : ParseableType System.FilePath where
  name := "System.FilePath"
  parse? str := some { toString := str }

/-- Convert parsed CLI arguments to SafeVerify Settings -/
def settingsFromParsed (p : Parsed) : SafeVerify.Settings where
  targetFile := p.positionalArg! "target" |>.as! System.FilePath
  submissionFile := p.positionalArg! "submission" |>.as! System.FilePath
  disallowPartial := p.hasFlag "disallow-partial"
  verbose := p.hasFlag "verbose"
  allowedAxioms := #[`propext, `Quot.sound, `Classical.choice]
  jsonOutputPath := p.flag? "save" |>.map (·.as! System.FilePath)
  allowDisproofs := p.hasFlag "disproofs"

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
  IO.eprintln s!"Currently running on Lean v{Lean.versionString}"

  -- Create settings from CLI arguments
  let settings := settingsFromParsed p
  IO.eprintln s!"Running SafeVerify on target file: {settings.targetFile} and submission file: {settings.submissionFile}."

  -- Replay files to get declarations (runs in ReaderT Settings IO)
  IO.eprintln "------------------"
  let (targetDecls, env) ← replayChallenges.run settings
  IO.eprintln "------------------"
  let submissionDecls ← replaySolutions.run settings

  -- Create the Decls context (env from target file, used for disproof checking)
  let decls : SafeVerify.Decls := {
    targetDecls := targetDecls,
    submissionDecls := submissionDecls,
    env := env
  }

  -- Run the main SafeVerify check (runs in ReaderT Settings (ReaderT Decls (StateT State IO)))
  let (_, finalState) ← (runSafeVerify.run settings |>.run decls |>.run {})

  -- Save JSON output if requested
  if let some jsonPath := settings.jsonOutputPath then
    let jsonOutput := ToJson.toJson finalState.checkOutcomes.toArray
    IO.FS.writeFile jsonPath (ToString.toString jsonOutput)
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
    s, "save" : System.FilePath; "Save output to a JSON file"
    d, "disproofs"; "Allow disproof submissions (submission named foo.disproof proves foo)"

  ARGS:
    target : System.FilePath; "The target file"
    submission : System.FilePath; "The submission file"
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
