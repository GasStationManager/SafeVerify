/-
Adapted from https://github.com/leanprover/lean4checker/blob/master/Main.lean
and
https://github.com/kim-em/lean-training-data/blob/master/scripts/declaration_types.lean
-/

import Lean
import Cli

open Lean Meta Core

def Lean.ConstantInfo.kind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot" -- Not sure what this is!
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]

structure Info where
  name : Name
  constInfo : ConstantInfo
  axioms : Array Name
deriving Inhabited

instance : ToString Info where
  toString info := s!"Name: {info.name}. Axioms: {info.axioms}."

def checkAxioms (info : Info) : Bool := Id.run do
  for a in info.axioms do
    if a ∉ AllowedAxioms then return false
  return true

/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantInfo) (checkVal:Bool:=false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

/-
Check if two opaque constants are the same
-/
def equivOpaq (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .opaqueInfo tval₁ := ctarget | false
  let .opaqueInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.isUnsafe == tval₂.isUnsafe
    && tval₁.value == tval₂.value

open Std

/-- Takes the environment obtained after replaying all the constant in a file and outputs
a hashmap storing the infos corresponding to all the theorems and definitions in the file. -/
def processFileDeclarations
    (env : Environment) : IO <| HashMap Name Info := do
  -- let ctx : Core.Context := {fileName:="", fileMap:= default}
  let mut out : HashMap Name Info := {}
  for (n, ci) in env.constants.map₂  do
    if ci.kind ∈ ["theorem", "def", "opaque"] then
      -- IO.println "---"
      -- IO.println ci.kind
      -- IO.println n
      -- IO.println <| ← Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ci.type) ctx {env:= env})
      -- if ci.kind == "def" then
        -- IO.println s!":= {ci.value!}"
      let (_, s) := (CollectAxioms.collect n).run env |>.run {}
      -- IO.println s.axioms
      out := out.insert n ⟨n, ci, s.axioms⟩
  return out

/-- The failure modes that can occur when running the safeverify check on a single declaration. -/
inductive CheckFailure
  /-- Used when the check failed because the declaration submitted has the wrong kind, e.g. is a theorem
  instead of a def. -/
  | kind (kind1 kind2 : String)
  /-- Used when the declaration is a theorem but has a different type to the target theorem. -/
  | thmType
  /-- Used when the declaration is a definition but has a different type or value to the target. -/
  | defnCheck
  /-- Used when the declaration is opaque but has a different type or value to the target. -/
  | opaqueCheck
  /-- Used when the value of a declaration uses a forbiden axiom. -/
  | axioms
  /-- Used when the corresponding target declaration wasn't found.-/
  | notFound

/-- The outcome of running the check on a single declaration in the submission. This contains:
1. The contant (stored as an `Info`).
2. The corresponding constant in the target file, if found.
3. The failure mode that occured, if the check failed. -/
structure SafeVerifyOutcome where
  submissionConstant : Info
  targetConstant : Option ConstantInfo
  failureMode : Option CheckFailure
deriving Inhabited

/-- Takes two arrays of `Info` and check that the declarations match (i.e. same kind, same type, and same
value if they are definitions). -/
def checkTargets (constants targets : HashMap Name Info) : (HashMap Name SafeVerifyOutcome) :=
  targets.map fun _ info ↦ Id.run do
    let ⟨n, ci, axs⟩ := info
    if let some info' := constants.get? n then
      let ci' := info'.constInfo
      if ci.kind ≠ ci'.kind then
        return {submissionConstant := info, targetConstant := ci', failureMode := some <| .kind ci.kind ci'.kind}
      if ci'.kind == "theorem" && !equivThm ci ci' then
        return {submissionConstant := info, targetConstant := ci', failureMode := some .thmType}
      if ci'.kind == "def" && !equivDefn ci ci' (`sorryAx ∉ axs)  then
        return {submissionConstant := info, targetConstant := ci', failureMode := some .defnCheck}
      if ci'.kind == "opaque" && !equivOpaq ci ci' then
        return {submissionConstant := info, targetConstant := ci', failureMode := some .opaqueCheck}
      if !checkAxioms info' then
        return {submissionConstant := info, targetConstant := ci', failureMode := some .axioms}
      return {submissionConstant := info, targetConstant := ci', failureMode := none}
    else
      return {submissionConstant := info, targetConstant := none, failureMode := some .notFound}

/-- Replays a lean file and outputs a hashmap storing the `Info`s corresponding to
the theorems and definitions in the file. -/
def replayFile (filePath : System.FilePath) (disallowPartial : Bool) : IO (HashMap Name _root_.Info) := do
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

/-- Run the main SafeVerify check on a pair of file (the targetFile containing statements and the
submission file containing proofs). -/
def runSafeVerify (targetFile submissionFile : System.FilePath) (disallowPartial : Bool) : IO Unit := do
  IO.println "------------------"
  let targetInfo ← replayFile targetFile
  IO.println "------------------"
  let submissionInfo ← replayFile submissionFile disallowPartial
  let checkOutcome := checkTargets submissionInfo targetInfo
  IO.println "------------------"
  for (name, ⟨_, _, failure?⟩) in checkOutcome do
    if failure?.isSome then
    IO.eprintln s!"Found a problem in {submissionFile} with declaration {name}"
  IO.println "------------------"
  IO.println s!"Finished."
  -- TODO: change this
  return

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
  let targetFile  := p.positionalArg! "target" |>.as! System.FilePath
  let submissionFile  := p.positionalArg! "submission" |>.as! System.FilePath
  IO.println s!"Running SafeVerify on target file: {targetFile} and submission file: {submissionFile}."
  runSafeVerify targetFile submissionFile disallowPartial
  return 0

/-- The main CLI interface for `SafeVerify`. This will be expanded as we add more
functionalities.-/
def mainCmd : Cmd := `[Cli|
  mainCmd VIA runMain;
  "Run SafeVerify on a pair of files (TargetFile, SubmissionFile). "
  -- TODO: add flags to control which axioms and allowed and so on.
  FLAGS:
    "disallow-partial"; "Disallow partial definitions"

  ARGS:
    target : System.FilePath; "The target file"
    submission : System.FilePath; "The submission file"
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
