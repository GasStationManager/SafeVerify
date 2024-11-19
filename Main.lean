/-
Adapted from https://github.com/leanprover/lean4checker/blob/master/Main.lean
and
https://github.com/kim-em/lean-training-data/blob/master/scripts/declaration_types.lean
-/

import Lean
import Lean.CoreM
import Lean.Replay
import Lean.Environment
import Lean.Util.CollectAxioms
import Batteries.Tactic.OpenPrivate

open Lean Meta Core
open private setImportedEntries finalizePersistentExtensions from Lean.Environment

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

def checkAxioms (env: Environment) (n: Name): IO Unit:= do
  let (_,s):=(CollectAxioms.collect n).run env |>.run {}
  for a in s.axioms do
    if a ∉ AllowedAxioms then
      throw <| IO.userError s!"{a} is not in the allowed set of standard axioms"

structure Info where
  name: Name
  constInfo: ConstantInfo
  axioms: Array Name
  nonComputable: Bool
  deriving Inhabited

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
def equivDefn (ctarget cnew : ConstantInfo)(checkVal:Bool:=false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value==tval₂.value else true)

unsafe def replayFile (mFile : System.FilePath)(targets: Array Info:=#[]) : IO <| Array Info := do
  IO.println s!"Replaying {mFile}"
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' does not exist"
  let (mod, region) ← readModuleData mFile
  --let (_, s) ← importModulesCore mod.imports
  --  |>.run (s := { moduleNameSet := ({} : NameHashSet) })
  --let env ← finalizeImport s #[] {} 0
  let env ← importModules mod.imports {} 0
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let mut env' ← env.replay newConstants
  --env' ← setImportedEntries env' #[mod]
  --env' ← finalizePersistentExtensions env' #[mod] {}
  let testnc:=isNoncomputable env `Classical.ofNonempty
  let testnc':=isNoncomputable env' `Classical.ofNonempty
  IO.println s!"Classical.ofNonempty: {testnc} {testnc'}"
  let ctx:={fileName:="", fileMap:=default}
  let mut ret:Array Info:= #[]
  for (n,ci) in env'.constants.map₂  do
    if ci.kind ∈ ["theorem", "def"] then
      IO.println "---"
      IO.println ci.kind
      IO.println n
      IO.println <| ←  Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ci.type) ctx {env:=env'})
      if ci.kind=="def" then
        IO.println s!":= {ci.value!}"
      let (_,s):=(CollectAxioms.collect n).run env' |>.run {}
      IO.println s.axioms
      let nc:=isNoncomputable env' n
      IO.println s!"noncomputable: {nc}"
      ret:=ret.push ⟨ n,ci,s.axioms, nc⟩
  if targets.size>0 then
    for ⟨ n,ci,axs, nc⟩ in targets do
      if let some ci':=env'.constants.map₂.find? n then
        if ci.kind ≠ ci'.kind then
          throw <| IO.userError s!"{ci'.kind} {n} is not the same kind as the requirement {ci.kind} {n}"
        if ci'.kind=="theorem" then
          if Not (equivThm ci ci') then
            throw <| IO.userError s!"theorem {n} does not have the same type as the requirement"
        if ci'.kind=="def" then
          if Not (equivDefn ci ci' (`sorryAx ∉ axs)) then
            throw <| IO.userError s!"definition {n} does not match the requirement"
          if (¬ nc) && isNoncomputable env' n then
            throw <| IO.userError s!"definition {n} is noncomputable"
        checkAxioms env' n
      else
        throw <| IO.userError s!"{n} not found in submission"
  env'.freeRegions
  region.free
  return ret

/-
Takes two olean files, and checks whether the second file
implements the theorems and definitions specified in the first file.
First file (the target) may contain theorem / function signature with sorry in their bodies;
the second file is expected to fill them.
Uses Environment.replay to defend against manipulation of environment.
Checks the second file's theorems to make sure they only use the three standard axioms.
-/
unsafe def main (args : List String) : IO UInt32 := do
  if args.length<2 then
    throw <| IO.userError s!"not enough arguments"
  let targf:System.FilePath := args[0]!
  let submf:System.FilePath := args[1]!
  let targInfo ← replayFile targf
  discard <| replayFile submf targInfo
  IO.println s!"Finished with no errors."
  return 0
