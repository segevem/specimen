import Plausible.Gen
import Specimen.DecOpt
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.EnumeratorCombinators
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveEnum

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

inductive typ where
  | Nat : typ
  | Fun : typ → typ → typ
  deriving DecidableEq, Repr

deriving instance Enum for typ

-- instance : BEq typ := instBEqOfDecidableEq

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: typ → term → term
  deriving BEq, Repr

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : List typ -> Nat -> typ -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive typing: List typ → term → typ → Prop where
| TConst : ∀ Γ n,
    typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2,
    typing Γ e1 .Nat →
    typing Γ e2 .Nat →
    typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ Γ e τ1 τ2,
    typing (τ1::Γ) e τ2 →
    typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    typing Γ e2 τ1 →
    typing Γ e1 (.Fun τ1 τ2) →
    typing Γ (.App e1 e2) τ2

set_option maxHeartbeats 800000
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

-- BUG: derive_mutual should auto-derive the DecOpt (checker) instances needed by the
-- generator schedule, but currently only auto-derives `.relation` deps, not `.checker` deps.
-- This fails with: "failed to synthesize instance of type class DecOpt (typing ...)"
derive_mutual
  (fun Γ e => ∃ (τ : typ), typing Γ e τ)

-- To sample from this generator and print out 10 successful examples using the `Repr`
-- instance for `term`, we can run the following:
-- #eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => typing [] e $ .Fun .Nat .Nat) 3) 3
