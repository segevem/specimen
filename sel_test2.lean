import Specimen
open Plausible Scoring Schedules
open Specimen

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxRecDepth 8000

/-- Recursive expression language; `app` mirrors `.call`. -/
inductive Exp where
  | lit  : Nat → Exp
  | app  : Nat → List Exp → Exp
  | pair : Exp → Exp → Exp
  deriving Repr, Inhabited

deriving instance DecidableEq for Exp

/-- Types. -/
inductive Ty where
  | base : Nat → Ty
  | prod : Ty → Ty → Ty
  deriving Repr, DecidableEq, Inhabited

/-- Finite, ground-pinning signature relation (mirrors `HasTypeCall`): pins
    `(fn, argTys, resultTy)` to literal signatures. `argTys` (pos 1) is the
    selectivity target — also openly producible by `WTList`. -/
inductive FnSig : Nat → List Ty → Ty → Prop where
  | f0 : FnSig 0 [Ty.base 1] (Ty.base 2)
  | f1 : FnSig 1 [Ty.base 2, Ty.base 2] (Ty.base 3)
  | f2 : FnSig 2 [] (Ty.base 1)

/-- Finite pinner for literals: pins the result type (pos 1) but leaves the
    literal value `n` (pos 0) free (an unavoidable-open variable). -/
inductive PrimTy : Nat → Ty → Prop where
  | p : ∀ n, PrimTy n (Ty.base 0)

/-- Mutually recursive well-typedness (mirrors `HasType` / `HasTypeList`). -/
mutual
inductive WT : Exp → Ty → Prop where
  | lit  : ∀ n t, PrimTy n t → WT (Exp.lit n) t
  | pair : ∀ a b ta tb, WT a ta → WT b tb → WT (Exp.pair a b) (Ty.prod ta tb)
  | app  : ∀ fn args tys t, WTList args tys → FnSig fn tys t → WT (Exp.app fn args) t
inductive WTList : List Exp → List Ty → Prop where
  | nil  : WTList [] []
  | cons : ∀ x xs t ts, WT x t → WTList xs ts → WTList (x :: xs) (t :: ts)
end

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
derive_mutual
  generator (fun t => ∃ e, WT e t)
