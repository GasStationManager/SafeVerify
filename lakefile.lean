import Lake

open Lake DSL

abbrev safeVerifyLeanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
]

package «SafeVerify» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0"

@[default_target]
lean_lib SafeVerify where
  leanOptions := safeVerifyLeanOptions
  globs := #[.submodules `SafeVerify, `Main]

@[test_driver]
lean_lib SafeVerifyTest where
  globs := #[.submodules `SafeVerifyTest]

lean_exe safe_verify where
  root := `Main
  supportInterpreter := true
