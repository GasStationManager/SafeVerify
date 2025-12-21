import Lake

open Lake DSL

abbrev safeVerifyLeanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
]

package SafeVerify

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.20.0"

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
