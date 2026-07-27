import Specimen.DeriveConstrainedProducer
import Plausible.Gen

/-!
# Weight Precomputation Tests

`set_option specimen.precomputeWeights true` partially evaluates each constructor's
weight function under the runtime `size` binder at elaboration time, so the generated
code carries a small residual expression in `size` rather than a full weight-function
call. This must be **semantics-preserving**: a generator derived with it has to produce
the exact same output as one derived without it on the same seed.

To compare the two without duplicating the inductive, we derive the *same* relation
twice under `scoped derive_mutual` in two namespaces — so each derivation produces a
namespace-scoped `ArbitrarySizedSuchThat` instance, selected unambiguously via `open`.

We use a **weight modifier that inspects the constructor name** (`nameCompareModifier`):
a per-pick `Name`/`String` match at runtime that partial evaluation folds to a
per-constructor constant, so precompute's impact is visible. We then:
1. assert both versions produce identical output over many deterministic seeds, and
2. report execution timing for both (informational; interpreter timing is noisy).
-/

open Plausible Scoring Schedules

inductive PrecompBetween : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, PrecompBetween lo hi lo
  | there : ∀ lo hi n, PrecompBetween (lo + 1) hi n → PrecompBetween lo hi n

/-- A weight modifier that branches on the constructor name — a `Name`/`String` match
    performed on every constructor pick at runtime. Partial evaluation reduces each
    per-constructor call (the name is a compile-time literal) to a constant. -/
def nameCompareModifier (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str _ "here"  => baseWeight * 2 + 1
  | .str _ "there" => baseWeight + 3
  | _              => baseWeight

initialize Scoring.registerWeightModifier `nameCompareModifier nameCompareModifier ``nameCompareModifier

-- `richOutput false` + `textOutput 3` make `derive_mutual` emit the generated code as
-- plain text, and `#guard_msgs (substring := true)` asserts an elucidating substring of
-- it — the weight expression baked into the `GeneratorCombinators.backtrack` list.

-- Version A: name-comparing modifier, weights evaluated at runtime (precompute off).
-- The generated code still contains the full `nameCompareModifier (balancedCtorWeight …)` call.
namespace Baseline
set_option specimen.richOutput false in
set_option specimen.textOutput 3 in
set_option specimen.weightModifier "nameCompareModifier" in
set_option specimen.precomputeWeights false in
set_option specimen.autoDeriveDeps true in
/-- (nameCompareModifier (Scoring.balancedCtorWeight -/
#guard_msgs (substring := true, whitespace := lax) in
scoped derive_mutual (fun (lo hi : Nat) => ∃ n, PrecompBetween lo hi n)
end Baseline

-- Version B: same modifier, weights partially evaluated at elaboration time (precompute on).
-- Each per-constructor weight folds to a constant / small size-expression:
--   `here`  → 33   (the whole name match + balanced computation collapses to a literal)
--   `there` → (if size' = 0 then 0 else max 1 size' * 4) + 3
namespace Precomputed
set_option specimen.richOutput false in
set_option specimen.textOutput 3 in
set_option specimen.weightModifier "nameCompareModifier" in
set_option specimen.precomputeWeights true in
set_option specimen.autoDeriveDeps true in
/-- [(33, return a_1), ((if size' = 0 then 0 else max 1 size' * 4) + 3, do -/
#guard_msgs (substring := true, whitespace := lax) in
scoped derive_mutual (fun (lo hi : Nat) => ∃ n, PrecompBetween lo hi n)
end Precomputed

-- Each snapshot binds the scoped instance from exactly one namespace.
open Baseline in
private def genOff (sz : Nat) : Gen Nat :=
  ArbitrarySizedSuchThat.arbitrarySizedST (fun n => PrecompBetween 0 30 n) sz
open Precomputed in
private def genOn (sz : Nat) : Gen Nat :=
  ArbitrarySizedSuchThat.arbitrarySizedST (fun n => PrecompBetween 0 30 n) sz

/-- Deterministic run of a `Gen` with an explicit `size` and RNG `seed`
    (`Gen.run` uses the global, non-reproducible RNG instead). -/
private def runSeeded (x : Gen Nat) (size seed : Nat) : Option Nat :=
  ((runRandWith seed x).run (ULift.up size)).toOption

private def sampleSeeded (gen : Nat → Gen Nat) (size trials : Nat) : Array (Option Nat) := Id.run do
  let mut out := Array.mkEmpty trials
  for i in [:trials] do
    out := out.push (runSeeded (gen size) size (1000 + i))
  return out

-- Correctness: identical output on identical seeds ⇒ partial evaluation preserved semantics.
/-- info: PASS -/
#guard_msgs in
#eval do
  let size := 12
  let trials := 3000
  if sampleSeeded genOff size trials == sampleSeeded genOn size trials then
    IO.println "PASS"
  else
    throw <| IO.userError "FAIL: precomputed generator diverged from baseline"

-- Best (minimum) elapsed nanos over `repeats` rounds, to damp interpreter scheduling noise.
-- The `acc` checksum is consumed (guards against dead-code elimination of the sampling loop).
private def bestTime (gen : Nat → Gen Nat) (size trials repeats : Nat) : IO Nat := do
  let _ := sampleSeeded gen size 100   -- warmup
  let mut best : Nat := 0
  for r in [:repeats] do
    let mut acc : Nat := 0
    let t0 ← IO.monoNanosNow
    for i in [:trials] do
      match runSeeded (gen size) size (1000 + i) with
      | some n => acc := acc + n
      | none => pure ()
    let t1 ← IO.monoNanosNow
    if acc == 0 then throw <| IO.userError "unexpected empty sampling run"
    best := if r == 0 then t1 - t0 else min best (t1 - t0)
  return best

-- Efficiency: the folded (precomputed) generator runs faster than the baseline, whose
-- weights — including the per-pick `nameCompareModifier` name match — are evaluated at
-- runtime. Silent on success; elapsed times are compared, not printed (nondeterministic).
/-- info: PASS -/
#guard_msgs in
#eval do
  let size := 12
  let trials := 30000
  let tBase ← bestTime genOff size trials 5
  let tPre ← bestTime genOn size trials 5
  if tBase > tPre then IO.println "PASS"
  else throw <| IO.userError s!"expected baseline ({tBase}ns) > precomputed ({tPre}ns)"
