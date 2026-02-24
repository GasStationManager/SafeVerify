import SafeVerify.Types
import Mathlib.Tactic.Push
import Lean

open Lean SafeVerify

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
def equivDefn (ctarget cnew : ConstantInfo) (checkVal : Bool := false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

/-
Check if two opaque constants are the same
-/
def equivOpaq (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .opaqueInfo tval₁ := ctarget | false
  let .opaqueInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.isUnsafe == tval₂.isUnsafe
    && tval₁.value == tval₂.value

open Elab Meta Term Tactic

def checkNegatedTheorem {m} [Monad m] [MonadLiftT CoreM m]
    (ctarget cnew : ConstantInfo) : m Bool :=
  -- We run in MetaM but don't really need any context
  Lean.Meta.MetaM.run' do
  unless ctarget.levelParams == cnew.levelParams do return false
  let targetType := ctarget.type
  let negatedType ← Meta.mkAppM ``Not #[targetType]
  let eqNeg ← Meta.mkAppM ``Eq #[negatedType, cnew.type]
  let pfTacs ← `(term| by push_neg; rfl)
  try
    let runTacs : TermElabM Expr := elabTermAndSynthesize pfTacs eqNeg
    let (goalMVar, _) ← runTacs.run
    let .ok proofType := Lean.Kernel.check (← getEnv) (← getLCtx) goalMVar | return false
    IO.eprintln "Checked disproof."
    match Lean.Kernel.isDefEq (← getEnv) (← getLCtx) proofType eqNeg with
    | .error _ => return false
    | .ok bool => return bool
  catch _ =>
    return false
