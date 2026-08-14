import Specimen.DeriveConstrainedProducer
import Plausible.Gen

/-!
# Generation-speed baseline benchmark

Establishes current throughput for derived generators so IR/combinator
optimizations can be measured against it. Not part of the test suite (it prints
nondeterministic timings); build explicitly with
`lake build SpecimenTest.GenerationBenchmark`.

Deterministic RNG seeding (`runRandWith`); reports the min elapsed over several
rounds to damp scheduling noise. NOTE: `#eval` runs in the interpreter, so
absolute numbers reflect the interpreted path — ratios/slopes are what transfer.
-/

open Plausible Scoring Schedules

private def runSeeded (x : Gen Nat) (size seed : Nat) : Option Nat :=
  ((runRandWith seed x).run (ULift.up size)).toOption

private def bench (label : String) (gen : Nat → Gen Nat) (size trials repeats : Nat) : IO Unit := do
  let mut w := 0
  for i in [:1000] do
    if (runSeeded (gen size) size (7 + i)).isSome then w := w + 1   -- warmup
  let mut best : Nat := 0
  let mut ok : Nat := 0
  let mut acc : Nat := 0
  for r in [:repeats] do
    let mut s := 0
    let t0 ← IO.monoNanosNow
    for i in [:trials] do
      match runSeeded (gen size) size (123000 + i) with
      | some n => s := s + 1; acc := acc + n
      | none => pure ()
    let t1 ← IO.monoNanosNow
    ok := s
    best := if r == 0 then t1 - t0 else min best (t1 - t0)
  let _ := acc
  IO.println s!"{label}  size={size}: {best / 1000000} ms / {trials}  ({best / trials} ns/gen, {ok}/{trials} ok)"

-- ── Relation A: 1 base + 1 recursive constructor (per-level / recursion cost) ─
inductive Rng : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, Rng lo hi lo
  | there : ∀ lo hi n, Rng (lo + 1) hi n → Rng lo hi n

set_option specimen.precomputeWeights false in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual (fun (lo hi : Nat) => ∃ n, Rng lo hi n)

private def rng (sz : Nat) : Gen Nat := ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Rng 0 200 n) sz

-- ── Relation B: flat relation, N check-guarded ctors, exactly one passes ─────
-- `IsEq k i` holds iff k = i (a check on the fixed input k). Each `Sel*` ctor is
-- guarded by such a check; for input k only the k-th ctor's check succeeds, so
-- the backtracking combinator must try (and unwind) the other N−1 failing
-- branches. Recursion depth is constant (all ctors are base), so ns/gen scaling
-- across N isolates the per-branch `pickDrop`/`sumFst`/`tryCatch` cost.
inductive IsEq : Nat → Nat → Prop where
  | mk : ∀ n, IsEq n n

inductive Sel4 : Nat → Nat → Prop where
  | c0 : ∀ k, IsEq k 0 → Sel4 k 0
  | c1 : ∀ k, IsEq k 1 → Sel4 k 1
  | c2 : ∀ k, IsEq k 2 → Sel4 k 2
  | c3 : ∀ k, IsEq k 3 → Sel4 k 3

inductive Sel8 : Nat → Nat → Prop where
  | c0 : ∀ k, IsEq k 0 → Sel8 k 0
  | c1 : ∀ k, IsEq k 1 → Sel8 k 1
  | c2 : ∀ k, IsEq k 2 → Sel8 k 2
  | c3 : ∀ k, IsEq k 3 → Sel8 k 3
  | c4 : ∀ k, IsEq k 4 → Sel8 k 4
  | c5 : ∀ k, IsEq k 5 → Sel8 k 5
  | c6 : ∀ k, IsEq k 6 → Sel8 k 6
  | c7 : ∀ k, IsEq k 7 → Sel8 k 7

inductive Sel16 : Nat → Nat → Prop where
  | c0  : ∀ k, IsEq k 0  → Sel16 k 0
  | c1  : ∀ k, IsEq k 1  → Sel16 k 1
  | c2  : ∀ k, IsEq k 2  → Sel16 k 2
  | c3  : ∀ k, IsEq k 3  → Sel16 k 3
  | c4  : ∀ k, IsEq k 4  → Sel16 k 4
  | c5  : ∀ k, IsEq k 5  → Sel16 k 5
  | c6  : ∀ k, IsEq k 6  → Sel16 k 6
  | c7  : ∀ k, IsEq k 7  → Sel16 k 7
  | c8  : ∀ k, IsEq k 8  → Sel16 k 8
  | c9  : ∀ k, IsEq k 9  → Sel16 k 9
  | c10 : ∀ k, IsEq k 10 → Sel16 k 10
  | c11 : ∀ k, IsEq k 11 → Sel16 k 11
  | c12 : ∀ k, IsEq k 12 → Sel16 k 12
  | c13 : ∀ k, IsEq k 13 → Sel16 k 13
  | c14 : ∀ k, IsEq k 14 → Sel16 k 14
  | c15 : ∀ k, IsEq k 15 → Sel16 k 15

set_option specimen.precomputeWeights false in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual (fun (k : Nat) => ∃ n, Sel4 k n)

set_option specimen.precomputeWeights false in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual (fun (k : Nat) => ∃ n, Sel8 k n)

set_option specimen.precomputeWeights false in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual (fun (k : Nat) => ∃ n, Sel16 k n)

-- Query the last index so a matching ctor always exists (uniqueness → backtrack).
private def sel4  (_sz : Nat) : Gen Nat := ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Sel4  3  n) 4
private def sel8  (_sz : Nat) : Gen Nat := ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Sel8  7  n) 4
private def sel16 (_sz : Nat) : Gen Nat := ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Sel16 15 n) 4

#eval do
  IO.println "── Rng (recursion cost) — size sweep ──"
  bench "rng" rng 0  50000 5
  bench "rng" rng 8  50000 5
  bench "rng" rng 32 50000 5
  IO.println "── Sel (backtrack cost) — N check-guarded ctors, exactly 1 passes ──"
  bench "sel4 " sel4  10 50000 5
  bench "sel8 " sel8  10 50000 5
  bench "sel16" sel16 10 50000 5
