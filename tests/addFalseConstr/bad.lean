import Batteries.Tactic.OpenPrivate

open private mk from Lean.Environment

open Lean in
elab "add_false_constructor" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `False.intro $ ConstantInfo.ctorInfo
      { name := `False.intro
        levelParams := []
        type := .const ``False []
        induct := `False
        cidx := 0
        numParams := 0
        numFields := 0
        isUnsafe := false }
    -- Before `Environment.mk` became private, we could just use
    -- `{ env with constants }`
    mk env.const2ModIdx constants env.extensions env.extraConstNames env.header

add_false_constructor

theorem falseThm : False :=
  False.intro
