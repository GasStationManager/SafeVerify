import Lean

open Lean Meta

namespace SafeVerify

-- TODO: later it could actually be nice to support printing out the actual declaration or so
-- (e.g. print the goal if it's a theorem, etc)
instance : ToJson ConstantInfo where
  toJson
    | .defnInfo _v    => Json.mkObj [("kind", "definition")]
    | .thmInfo _v     => Json.mkObj [("kind", "theorem")]
    | .axiomInfo _v   => Json.mkObj [("kind", "axiom")]
    | .opaqueInfo _v  => Json.mkObj [("kind", "opaque")]
    | .quotInfo _v    => Json.mkObj [("kind", "quotient")]
    | .inductInfo _v  => Json.mkObj [("kind", "inductive")]
    | .ctorInfo _v    => Json.mkObj [("kind", "constructor")]
    | .recInfo _v     => Json.mkObj [("kind", "recursor")]

structure Info where
  constInfo : ConstantInfo
  axioms : Array Name
deriving Inhabited, ToJson

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
deriving ToJson

/--
The outcome of running the check on a single declaration in the target. This contains:
1. The constant in the target file (stored as an `Info`).
2. The corresponding constant in the submission file, if found.
3. The failure mode that occured, if the check failed.
-/
structure SafeVerifyOutcome where
  targetInfo : Info
  solutionInfo : Option Info
  failureMode : Option CheckFailure
deriving Inhabited, ToJson

end SafeVerify
