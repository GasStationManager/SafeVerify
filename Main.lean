/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Replay
--import Lean4Checker.Lean
import Lake.Load.Manifest

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports
    |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
  let env ← finalizeImport s #[{module}] {} 0
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  for (n,_) in env.constants.toList do
    IO.println n
  env'.freeRegions
  region.free

unsafe def replayFromFresh (module : Name) : IO Unit := do
  Lean.withImportModules #[{module}] {} 0 fun env => do
    discard <| (← mkEmptyEnvironment).replay env.constants.map₁

/-- Read the name of the main module from the `lake-manifest`. -/
-- This has been copied from `ImportGraph.getCurrentModule` in the
-- https://github.com/leanprover-community/import-graph repository.
def getCurrentModule : IO Name := do
  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    -- TODO: should this be caught?
    pure .anonymous
  | some manifest =>
    -- TODO: This assumes that the `package` and the default `lean_lib`
    -- have the same name up to capitalisation.
    -- Would be better to read the `.defaultTargets` from the
    -- `← getRootPackage` from `Lake`, but I can't make that work with the monads involved.
    return manifest.name.capitalize


/--
Run as e.g. `lake exe lean4checker` to check everything in the current project.
or e.g. `lake exe lean4checker Mathlib.Data.Nat` to check everything with module name
starting with `Mathlib.Data.Nat`.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4checker --fresh Mathlib.Data.Nat.Prime.Basic`
to replay all the constants (both imported and defined in that file) into a fresh environment.
This can only be used on a single file.

This is not an external verifier, simply a tool to detect "environment hacking".
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let verbose := "-v" ∈ flags || "--verbose" ∈ flags
  let targets ← do
    args.mapM fun arg => do
      let mod := arg.toName
      if mod.isAnonymous then
        throw <| IO.userError s!"Could not resolve module: {arg}"
      else
        pure mod
  let mut targetModules := #[]
  let sp ← searchPathRef.get
  for target in targets do
    let mut found := false
    for path in (← SearchPath.findAllWithExt sp "olean") do
      if let some m := (← searchModuleNameOfFileName path sp) then
        if target.isPrefixOf m then
          targetModules := targetModules.push m
          found := true
    if not found then
      throw <| IO.userError s!"Could not find any oleans for: {target}"
  if "--fresh" ∈ flags then
    if targetModules.size != 1 then
      throw <| IO.userError "--fresh flag is only valid when specifying a single module"
    for m in targetModules do
      if verbose then IO.println s!"replaying {m} with --fresh"
      replayFromFresh m
  else
    let mut tasks := #[]
    for m in targetModules do
      tasks := tasks.push (m, ← IO.asTask (replayFromImports m))
    for (m, t) in tasks do
      if verbose then IO.println s!"replaying {m}"
      if let .error e := t.get then
        IO.eprintln s!"lean4checker found a problem in {m}"
        throw e
  return 0
