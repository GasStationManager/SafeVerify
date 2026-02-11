import SafeVerify.Types

open Lean SafeVerify

instance : ToString DefinitionSafety where
  toString
    | .safe => "safe"
    | .unsafe => "unsafe"
    | .partial => "partial"

def Lean.ConstantInfo.kind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot" -- Not sure what this is!
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

instance : ToString CheckFailure where
  toString
    | .kind k1 k2 => s!"kind mismatch (expected {k1}, got {k2})"
    | .thmType => "theorem type mismatch"
    | .defnCheck => "definition type or value mismatch"
    | .opaqueCheck => "opaque type or value mismatch"
    | .axioms => "uses disallowed axioms"
    | .notFound => "declaration not found in submission"

instance : ToString Info where
  toString info := s!"Name: {info.constInfo.name}. Axioms: {info.axioms}."
