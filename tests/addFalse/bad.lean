import Batteries.Tactic.OpenPrivate

open private mk from Lean.Environment

open Lean in
elab "add_false" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `false $ ConstantInfo.thmInfo
      { name := `false, levelParams := [], type := .const ``False [], value := .const ``False [] }
    -- Before `Environment.mk` became private, we could just use
    -- `{ env with constants }`
    mk env.const2ModIdx constants env.extensions env.extraConstNames env.header

add_false

theorem falseThm : False :=
   false
