/-
Adapted from https://github.com/leanprover/lean4checker/blob/master/Main.lean
and
https://github.com/kim-em/lean-training-data/blob/master/scripts/declaration_types.lean
-/

import SafeVerify
import Lean
import Cli

-- TODO(Paul-Lez): it would be nice to do things monadically here!

open Lean Meta Core SafeVerify

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]

def checkAxioms (info : Info) : Bool := Id.run do
  for a in info.axioms do
    if a ∉ AllowedAxioms then return false
  return true

open Std

/-- Takes the environment obtained after replaying all the constant in a file and outputs
a hashmap storing the infos corresponding to all the theorems and definitions in the file. -/
def processFileDeclarations (env : Environment) : HashMap Name Info := Id.run do
  let mut out : HashMap Name Info := {}
  for (_, ci) in env.constants.map₂  do
    if ci.kind ∈ ["theorem", "def", "opaque", "inductive", "constructor"] then
      let (_, s) := (CollectAxioms.collect ci.name).run env |>.run {}
      out := out.insert ci.name ⟨ci, s.axioms⟩
  return out

def Info.toFailureMode (target submission : Info) : Option SafeVerifyOutcome := Id.run do
  if target.constInfo.kind ≠ submission.constInfo.kind then
    return some ⟨target, submission, some <| .kind target.constInfo.kind submission.constInfo.kind⟩
  -- This is a little hacky since it would be better to avoid string matching but let's deal with that later.
  if submission.constInfo.kind == "theorem" && !equivThm target.constInfo submission.constInfo then
    return some ⟨target, submission, some .thmType⟩
  if submission.constInfo.kind == "def"
      && !equivDefn target.constInfo submission.constInfo (`sorryAx ∉ target.axioms)  then
    return some ⟨target, submission, some .defnCheck⟩
  if submission.constInfo.kind == "opaque" && !equivOpaq target.constInfo submission.constInfo then
    return some ⟨target, submission, some .opaqueCheck⟩
  if submission.constInfo.kind == "constructor" && !equivCtor target.constInfo submission.constInfo then
    return some ⟨target, submission, some .ctorCheck⟩
  if !checkAxioms submission then
    return some ⟨target, submission, some .axioms⟩
  return some ⟨target, submission, none⟩

/-- Takes two arrays of `Info` and check that the declarations match (i.e. same kind, same type, and same
value if they are definitions). -/
def checkTargets (targetInfos submissionInfos : HashMap Name Info) : HashMap Name SafeVerifyOutcome :=
  -- Create lookup functions for equivInduct (needs access to full hashmaps for constructor lookup)
  let lookupTarget := fun n => targetInfos.get? n |>.map (·.constInfo)
  let lookupNew := fun n => submissionInfos.get? n |>.map (·.constInfo)
  targetInfos.map fun _ targetInfo ↦ Id.run do
    let optionInfo := submissionInfos.get? targetInfo.constInfo.name
    -- For inductives, check via equivInduct which needs the full hashmaps for constructor lookup
    if targetInfo.constInfo.kind == "inductive" then
      if let some submissionInfo := optionInfo then
        if targetInfo.constInfo.kind ≠ submissionInfo.constInfo.kind then
          return ⟨targetInfo, some submissionInfo, some <| .kind targetInfo.constInfo.kind submissionInfo.constInfo.kind⟩
        if !equivInduct targetInfo.constInfo submissionInfo.constInfo lookupTarget lookupNew then
          return ⟨targetInfo, some submissionInfo, some .inductCheck⟩
        if !checkAxioms submissionInfo then
          return ⟨targetInfo, some submissionInfo, some .axioms⟩
        return ⟨targetInfo, some submissionInfo, none⟩
      else
        return ⟨targetInfo, none, some .notFound⟩
    let optionOutcome := optionInfo.bind (Info.toFailureMode targetInfo)
    optionOutcome.getD (dflt := ⟨targetInfo, none, some .notFound⟩)

/-- Deep-copy a universe level, rebuilding every node from scratch.
This breaks references to corrupted Level objects (e.g., via unsafeCast). -/
partial def rebuildLevel : Level → Level
  | .zero => .zero
  | .succ l => .succ (rebuildLevel l)
  | .max l1 l2 => .max (rebuildLevel l1) (rebuildLevel l2)
  | .imax l1 l2 => .imax (rebuildLevel l1) (rebuildLevel l2)
  | .param n => .param n
  | .mvar id => .mvar id

/-- Deep-copy an expression, rebuilding every node from scratch.
This breaks references to compacted regions whose runtime representation
may have been corrupted (e.g., via unsafeCast at elaboration time). -/
partial def rebuildExpr : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort l => .sort (rebuildLevel l)
  | .const n ls => .const n (ls.map rebuildLevel)
  | .lit (.natVal n) => .lit (.natVal n)
  | .lit (.strVal s) => .lit (.strVal s)
  | .app f a => .app (rebuildExpr f) (rebuildExpr a)
  | .lam n t b bi => .lam n (rebuildExpr t) (rebuildExpr b) bi
  | .forallE n t b bi => .forallE n (rebuildExpr t) (rebuildExpr b) bi
  | .letE n t v b nd => .letE n (rebuildExpr t) (rebuildExpr v) (rebuildExpr b) nd
  | .mdata m e => .mdata m (rebuildExpr e)
  | .proj s i e => .proj s i (rebuildExpr e)

/-- Sanitize a ConstantInfo by rebuilding all literals in its value/type.
This ensures the kernel re-evaluates literals from scratch during replay. -/
def sanitizeConstant : ConstantInfo → ConstantInfo
  | .defnInfo d => .defnInfo { d with
      type := rebuildExpr d.type
      value := rebuildExpr d.value }
  | .thmInfo t => .thmInfo { t with
      type := rebuildExpr t.type
      value := rebuildExpr t.value }
  | .opaqueInfo o => .opaqueInfo { o with
      type := rebuildExpr o.type
      value := rebuildExpr o.value }
  | ci => ci

def replayFile (filePath : System.FilePath) (disallowPartial : Bool) : IO (HashMap Name Info) := do
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
    newConstants := newConstants.insert name (sanitizeConstant ci)
  let env ← env.replay newConstants
  IO.eprintln s!"Finished replay. Found {newConstants.size} declarations."
  -- Verify theorem proofs using kernel typechecker with rebuilt expressions.
  -- This catches attacks where corrupted compacted-region values (e.g., from
  -- unsafeCast at elaboration time) cause the kernel to accept invalid proofs.
  for name in mod.constNames, ci in mod.constants do
    if let .thmInfo t := ci then
      let freshValue := rebuildExpr t.value
      let freshType := rebuildExpr t.type
      match Kernel.check env {} freshValue with
      | .ok inferredType =>
        match Kernel.isDefEq env {} inferredType freshType with
        | .ok true => pure ()
        | _ => throw <| IO.userError s!"kernel verification failed for '{name}': inferred type does not match declared type"
      | .error _ =>
        throw <| IO.userError s!"kernel verification failed for '{name}': proof term rejected by kernel typechecker (possible unsafeCast or compacted-region corruption)"
  return processFileDeclarations env

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
      -- probably we should track disallowed opaque (and partial) constant in a CheckFailureField.
      IO.eprintln s!"  Safety mismatch: expected isUnsafe={tval₁.isUnsafe}, got isUnsafe={tval₂.isUnsafe}"
    if tval₁.value != tval₂.value then
      IO.eprintln s!"  Value mismatch (values differ)"

/-- Read module imports from an olean file without full replay. -/
def readImports (filePath : System.FilePath) : IO (Array Import) := do
  unless (← filePath.pathExists) do
    throw <| IO.userError s!"object file '{filePath}' does not exist"
  let (mod, _) ← readModuleData filePath
  return mod.imports

/-- Check that submission imports are a superset of target imports.
This prevents attacks where submissions omit imports to redefine types. -/
def checkImportSuperset (targetFile submissionFile : System.FilePath)
    (targetImports submissionImports : Array Import) : IO Unit := do
  -- Both target and submission must import Init
  unless targetImports.any (·.module == `Init) do
    throw <| IO.userError s!"Target '{targetFile}' does not import Init. Refusing to verify against a prelude-based target."
  if submissionImports.isEmpty then
    throw <| IO.userError s!"'{submissionFile}' has no imports (possible prelude file). Submissions must import Init to prevent kernel type redefinition."
  -- Check that every target import appears in submission imports
  let submissionModules := submissionImports.map (·.module)
  let mut missing : Array Name := #[]
  for imp in targetImports do
    unless submissionModules.contains imp.module do
      missing := missing.push imp.module
  unless missing.isEmpty do
    throw <| IO.userError s!"Submission '{submissionFile}' is missing imports required by target: {missing}. Submissions must import at least everything the target imports to prevent type redefinition attacks."

/-- Recursively find all Nat literals in an expression. -/
partial def collectNatLiterals : Expr → Array (Nat × String)
  | .lit (.natVal n) =>
    let shown := toString (Expr.lit (.natVal n))
    #[(n, shown)]
  | .app f a => collectNatLiterals f ++ collectNatLiterals a
  | .lam _ t b _ => collectNatLiterals t ++ collectNatLiterals b
  | .forallE _ t b _ => collectNatLiterals t ++ collectNatLiterals b
  | .letE _ t v b _ => collectNatLiterals t ++ collectNatLiterals v ++ collectNatLiterals b
  | .mdata _ e => collectNatLiterals e
  | .proj _ _ e => collectNatLiterals e
  | _ => #[]

def validateNewDefinitionNatLiterals
    (targetInfos submissionInfos : HashMap Name Info) : IO Unit := do
  for (name, info) in submissionInfos do
    if targetInfos.get? name |>.isNone then
      let exprs := match info.constInfo with
        | .defnInfo d => #[d.type, d.value]
        | .thmInfo t => #[t.type, t.value]
        | .opaqueInfo o => #[o.type, o.value]
        | .inductInfo i => #[i.type]
        | .ctorInfo c => #[c.type]
        | .recInfo r => #[r.type]
        | _ => #[]
      for e in exprs do
        for (n, shown) in collectNatLiterals e do
          if shown.startsWith "-" then
            throw <| IO.userError s!"suspicious Nat literal in new declaration '{name}': stored natVal={n} but renders as '{shown}' (possible unsafeCast corruption)"

def runSafeVerify (targetFile submissionFile : System.FilePath)
    (disallowPartial : Bool) (verbose : Bool := false) :
    IO <| (HashMap Name SafeVerifyOutcome) × Bool := do
  let mut hasFailures := false
  -- Import superset check: submission must import everything the target does
  let targetImports ← readImports targetFile
  let submissionImports ← readImports submissionFile
  checkImportSuperset targetFile submissionFile targetImports submissionImports
  IO.eprintln "------------------"
  let targetInfo ← replayFile targetFile disallowPartial
  IO.eprintln "------------------"
  let submissionInfo ← replayFile submissionFile disallowPartial
  validateNewDefinitionNatLiterals targetInfo submissionInfo
  for (n, info) in submissionInfo do
    if !checkAxioms info then
      IO.eprintln s!"{n} used disallowed axioms. {info.axioms}"
      hasFailures := true
  let checkOutcome := checkTargets targetInfo submissionInfo
  IO.eprintln "------------------"

  for (name, outcome) in checkOutcome do
    if let some failure := outcome.failureMode then
      hasFailures := true
      IO.eprintln s!"Found a problem in {submissionFile} with declaration {name}: {failure}"
      if verbose then
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
          if let some submissionInfo := submissionInfo.get? name then
            IO.eprintln s!"  Disallowed axioms used: {submissionInfo.axioms.filter (· ∉ AllowedAxioms)}"
        | _ => pure ()
  IO.eprintln "------------------"
  return (checkOutcome, hasFailures)

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
  IO.eprintln s!"Currently running on Lean v{Lean.versionString}"
  let disallowPartial := p.hasFlag "disallow-partial"
  let verbose := p.hasFlag "verbose"
  let targetFile := p.positionalArg! "target" |>.as! System.FilePath
  let submissionFile := p.positionalArg! "submission" |>.as! System.FilePath
  IO.eprintln s!"Running SafeVerify on target file: {targetFile} and submission file: {submissionFile}."
  let (output, hasFailures) ← runSafeVerify targetFile submissionFile disallowPartial verbose
  let jsonOutput := ToJson.toJson output.toArray
  if let some jsonPathFlag := p.flag? "save" then
    let jsonPath := jsonPathFlag.as! System.FilePath
    IO.FS.writeFile jsonPath (ToString.toString jsonOutput)
  if hasFailures then
    let nonVerboseMsg :=
      " For more diagnostic information about failures, run safe_verify with the -v (or --verbose) flag."
    throw <| IO.userError s!"SafeVerify check failed.{if !verbose then nonVerboseMsg else ""}"
  else
    IO.eprintln "SafeVerify check passed."
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

  ARGS:
    target : System.FilePath; "The target file"
    submission : System.FilePath; "The submission file"
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
