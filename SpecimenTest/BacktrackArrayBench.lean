import Specimen.DeriveConstrainedProducer
import Plausible.Gen

/-!
# `backtrack` list-vs-array microbenchmark

Isolates the **selection overhead** of the backtracking combinator (not generation):
`n` weight-1 branches, and we measure the cost of driving `backtrack` through them.

Three variants:
- `list`  — current `GeneratorCombinators.backtrack` (List `pickDrop`, O(len) rebuild/pick)
- `array` — `backtrackArr` (Array swap-remove, O(len) scan but allocation-free)
- `unif`  — array + O(1) uniform index (no weighted scan; valid when weights are equal)

Two workloads:
- `allfail` — every branch throws → forces exactly `n` picks (max selection work)
- `oneok`   — last branch succeeds → random position, ~n/2 picks (realistic)

`#eval` runs interpreted, so ratios/slopes transfer, not absolute ns.
-/

open Plausible GeneratorCombinators

private def failBr : Gen Nat := throw Plausible.Gen.genericFailure
private def okBr : Gen Nat := pure 0

private def mkAllFail (n : Nat) : List (Nat × Gen Nat) :=
  (List.range n).map (fun _ => (1, failBr))
private def mkOneOk (n : Nat) : List (Nat × Gen Nat) :=
  (List.range n).map (fun i => (1, if i + 1 == n then okBr else failBr))

/-- Uniform-weight variant: O(1) index draw + O(1) swap-remove, no weighted scan. -/
private def btUnifFuel (steps : Nat) (default : Gen Nat) (arr : Array (Nat × Gen Nat)) (len : Nat) : Gen Nat :=
  match steps with
  | .zero => throw Plausible.Gen.genericFailure
  | .succ steps' => do
    if len == 0 then throw Plausible.Gen.genericFailure
    else
      let ⟨idx, _⟩ ← Gen.choose Nat 0 (len - 1) (by omega)
      let chosen := (arr[idx]?).getD (0, default)
      let arr := arr.set! idx ((arr[len - 1]?).getD (0, default))
      tryCatch chosen.2 (fun _ => btUnifFuel steps' default arr (len - 1))

private def btUnif (gs : Array (Nat × Gen Nat)) : Gen Nat :=
  btUnifFuel gs.size failBr gs gs.size

/-- Try branches in a precomputed order, backtracking on failure. -/
private partial def tryInOrder (arr : Array (Float × Gen Nat)) (i : Nat) : Gen Nat :=
  match arr[i]? with
  | some (_, g) => tryCatch g (fun _ => tryInOrder arr (i + 1))
  | none => throw Plausible.Gen.genericFailure

/-- Weighted shuffle (Efraimidis–Spirakis): key `kᵢ = -ln(uᵢ)/wᵢ`, sort ascending once,
    then walk the order. O(n) keys + O(n log n) sort, O(1)/attempt, no per-pick drop. -/
private def btShuffle (gs : Array (Nat × Gen Nat)) : Gen Nat := do
  let mut keyed : Array (Float × Gen Nat) := Array.mkEmpty gs.size
  for (w, g) in gs do
    let ⟨r, _⟩ ← Gen.choose Nat 1 1000000 (by omega)
    let u := Float.ofNat r / 1000001.0
    let key := (- Float.log u) / Float.ofNat w          -- ~Exp(wᵢ); smaller = picked first
    keyed := keyed.push (key, g)
  tryInOrder (keyed.qsort (fun a b => a.1 < b.1)) 0

/-- Stochastic-acceptance weighted index: draw uniform idx + uniform `r < wmax`, accept iff
    `r < w[idx]`. Exact `∝ w`, integer-only. `fuel` bounds rejections (degenerate all-zero case). -/
private partial def stochPick (arr : Array (Nat × Gen Nat)) (len wmax fuel : Nat) : Gen Nat := do
  let ⟨idx, _⟩ ← Gen.choose Nat 0 (len - 1) (by omega)
  match fuel with
  | 0 => return idx
  | fuel' + 1 =>
    let w := ((arr[idx]?).getD (0, failBr)).1
    let ⟨r, _⟩ ← Gen.choose Nat 0 (wmax - 1) (by omega)
    if r < w then return idx else stochPick arr len wmax fuel'

private partial def btStochFuel (steps : Nat) (arr : Array (Nat × Gen Nat)) (len wmax : Nat) : Gen Nat := do
  match steps with
  | 0 => throw Plausible.Gen.genericFailure
  | steps' + 1 =>
    if len == 0 then throw Plausible.Gen.genericFailure
    else
      let idx ← stochPick arr len wmax 64
      let chosen := (arr[idx]?).getD (0, failBr)
      let arr := arr.set! idx ((arr[len - 1]?).getD (0, failBr))
      tryCatch chosen.2 (fun _ => btStochFuel steps' arr (len - 1) wmax)

/-- Weighted `backtrack` via stochastic acceptance — integer-only, exact, early-exit, O(1) amortized
    per pick for bounded weight ratios (degenerates to the uniform draw when weights are equal). -/
private def btStoch (gs : Array (Nat × Gen Nat)) : Gen Nat :=
  btStochFuel gs.size gs gs.size (gs.foldl (fun m x => max m x.1) 0)

private def runG (x : Gen Nat) (seed : Nat) : Option Nat :=
  ((runRandWith seed x).run (ULift.up 10)).toOption

private def timeIt (label : String) (run : Nat → Option Nat) (trials : Nat) : IO Unit := do
  for i in [:2000] do let _ := run (7 + i)          -- warmup
  let mut best : Nat := 0
  let mut acc : Nat := 0
  for r in [:5] do
    let t0 ← IO.monoNanosNow
    for i in [:trials] do
      match run (123000 + i) with
      | some n => acc := acc + n
      | none => acc := acc + 1
    let t1 ← IO.monoNanosNow
    best := if r == 0 then t1 - t0 else min best (t1 - t0)
  IO.println s!"  {label}: {best / trials} ns/op   ({best / 1000000} ms / {trials})  [chk={acc % 7}]"

private def sweep (trials : Nat) : IO Unit := do
  for n in [4, 8, 16, 32, 71] do
    let gsF := mkAllFail n; let gaF := gsF.toArray
    let gsO := mkOneOk n;   let gaO := gsO.toArray
    IO.println s!"── n = {n} ──"
    timeIt "allfail list " (fun s => runG (backtrack gsF) s) trials
    timeIt "allfail array" (fun s => runG (backtrackArr gaF) s) trials
    timeIt "allfail unif " (fun s => runG (btUnif gaF) s) trials
    timeIt "allfail shuf " (fun s => runG (btShuffle gaF) s) trials
    timeIt "allfail stoch" (fun s => runG (btStoch gaF) s) trials
    timeIt "oneok   list " (fun s => runG (backtrack gsO) s) trials
    timeIt "oneok   unif " (fun s => runG (btUnif gaO) s) trials
    timeIt "oneok   stoch" (fun s => runG (btStoch gaO) s) trials

-- Skewed weights (alternating 1 / 16): only the weight-respecting variants are valid here.
private def mkSkewAllFail (n : Nat) : List (Nat × Gen Nat) :=
  (List.range n).map (fun i => (if i % 2 == 0 then 1 else 16, failBr))

private def skewSweep (trials : Nat) : IO Unit := do
  for n in [16, 71] do
    let gs := mkSkewAllFail n; let ga := gs.toArray
    IO.println s!"── skewed n = {n} (allfail) ──"
    timeIt "list " (fun s => runG (backtrack gs) s) trials
    timeIt "shuf " (fun s => runG (btShuffle ga) s) trials
    timeIt "stoch" (fun s => runG (btStoch ga) s) trials

#eval sweep 1000
#eval skewSweep 1000
