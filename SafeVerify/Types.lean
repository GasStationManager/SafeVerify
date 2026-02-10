import Lean

open Lean Meta

namespace SafeVerify

structure Info where
  name : Name
  constInfo : ConstantInfo
  axioms : Array Name
deriving Inhabited

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

/--
The outcome of running the check on a single declaration in the target. This contains:
1. The constant in the target file (stored as an `Info`).
2. The corresponding constant in the submission file, if found.
3. The failure mode that occured, if the check failed.
-/
structure SafeVerifyOutcome where
  targetInfo : Info
  submissionConstant : Option ConstantInfo
  failureMode : Option CheckFailure
deriving Inhabited


end SafeVerify
