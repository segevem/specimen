import Specimen
open Plausible Scoring Schedules
open Specimen

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3

/-- Finite, ground-pinning relation (mirrors `HasTypeCall` pinning `tys`):
    arg 0 (`t`) and arg 1 (`r`) are literal in every constructor. -/
inductive Sig : Nat → Nat → Prop where
  | a : Sig 1 10
  | b : Sig 2 20
  | c : Sig 3 30

/-- Open, recursive producer of `t` (mirrors `HasTypeList` producing `tys`). -/
inductive Peano : Nat → Prop where
  | z : Peano 0
  | s : ∀ n, Peano n → Peano (n + 1)

/-- `Foo r` needs a `t` with `Peano t` (open) and `Sig t r` (finite).
    Grounded schedule: produce `(t, r)` from `Sig`, then `check Peano t`.
    Bad (generate-and-test) schedule: `[t] ← Peano`, then `[r] ← Sig t r`. -/
inductive Foo : Nat → Prop where
  | mk : ∀ t r, Peano t → Sig t r → Foo r

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
derive_mutual
  generator (∃ r, Foo r)
