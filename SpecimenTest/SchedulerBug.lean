import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

namespace EqBindThenCheckRepro

/-- A DecOpt-checkable predicate on a `Nat`. -/
inductive Small : Nat → Prop where
  | mk : n ≤ 3 → Small n

instance (n : Nat) : DecOpt (Small n) where
  decOpt _ := if n ≤ 3 then .ok true else .ok false

-- WORKS: the output is written inline as `x + 1`, and the check is on that
-- term directly. The derived generator binds `y := x + 1` and DecOpt-checks `Small`.
inductive RWorks : Nat → Nat → Prop where
  | mk : ∀ x, Small (x + 1) → RWorks x (x + 1)

set_option specimen.autoDeriveDeps true in
derive_generator (fun x => ∃ y, RWorks x y)   -- ✅ derives

-- FAILS: logically identical, but `y` is a fresh output variable tied to
-- `x + 1` via a separate equality premise.
inductive RFails : Nat → Nat → Prop where
  | mk : ∀ x y, Small y → y = x + 1 → RFails x y

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
set_option specimen.scoreType "Scoring.DensityScore" in
derive_mutual (fun x => ∃ y, RFails x y)    -- ❌ fails to synthesize

end EqBindThenCheckRepro
