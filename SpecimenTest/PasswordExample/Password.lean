import Plausible.Gen
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.GeneratorCombinators
import Specimen.EnumeratorCombinators
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Specimen.DeriveEnum

/-!
# AWS IAM Default Password Policy

Generates and checks passwords satisfying the AWS IAM default policy:
- Length between 8 and 128
- Characters from at least 3 of 4 classes (upper, lower, digit, symbol)

The `CountClasses` relation walks a char list, classifying each character.
It works efficiently in both directions from a single definition:
- Forward (generator): given per-class counts, produce a password
- Backward (checker): given a password and counts, verify in O(n)

Reference: https://docs.aws.amazon.com/IAM/latest/UserGuide/id_credentials_passwords_account-policy.html
-/

open Plausible

namespace Password

/-! ## Character classes as inductive relations -/

inductive Upper : Char → Prop where
| A : Upper 'A' | B : Upper 'B' | C : Upper 'C' | D : Upper 'D'
| E : Upper 'E' | F : Upper 'F' | G : Upper 'G' | H : Upper 'H'
| I : Upper 'I' | J : Upper 'J' | K : Upper 'K' | L : Upper 'L'
| M : Upper 'M' | N : Upper 'N' | O : Upper 'O' | P : Upper 'P'
| Q : Upper 'Q' | R : Upper 'R' | S : Upper 'S' | T : Upper 'T'
| U : Upper 'U' | V : Upper 'V' | W : Upper 'W' | X : Upper 'X'
| Y : Upper 'Y' | Z : Upper 'Z'

inductive Lower : Char → Prop where
| a : Lower 'a' | b : Lower 'b' | c : Lower 'c' | d : Lower 'd'
| e : Lower 'e' | f : Lower 'f' | g : Lower 'g' | h : Lower 'h'
| i : Lower 'i' | j : Lower 'j' | k : Lower 'k' | l : Lower 'l'
| m : Lower 'm' | n : Lower 'n' | o : Lower 'o' | p : Lower 'p'
| q : Lower 'q' | r : Lower 'r' | s : Lower 's' | t : Lower 't'
| u : Lower 'u' | v : Lower 'v' | w : Lower 'w' | x : Lower 'x'
| y : Lower 'y' | z : Lower 'z'

inductive Digit : Char → Prop where
| d0 : Digit '0' | d1 : Digit '1' | d2 : Digit '2' | d3 : Digit '3'
| d4 : Digit '4' | d5 : Digit '5' | d6 : Digit '6' | d7 : Digit '7'
| d8 : Digit '8' | d9 : Digit '9'

inductive Symbol : Char → Prop where
| bang : Symbol '!' | at : Symbol '@' | hash : Symbol '#' | dollar : Symbol '$'
| pct : Symbol '%' | caret : Symbol '^' | amp : Symbol '&' | star : Symbol '*'
| lparen : Symbol '(' | rparen : Symbol ')' | under : Symbol '_' | plus : Symbol '+'
| dash : Symbol '-' | eq : Symbol '=' | lbrack : Symbol '[' | rbrack : Symbol ']'
| lbrace : Symbol '{' | rbrace : Symbol '}' | pipe : Symbol '|' | apos : Symbol '\''

/-! ## CountClasses: single relation for both generation and checking

`CountClasses cs nU nL nD nS` holds iff `cs` contains exactly `nU` uppercase,
`nL` lowercase, `nD` digit, and `nS` symbol characters.

- Generator direction: given counts → produce a char list
- Checker direction: given a char list and counts → verify
-/

inductive CountClasses : List Char → Nat → Nat → Nat → Nat → Prop where
| nil : CountClasses [] .zero .zero .zero .zero
| upper : Upper c → CountClasses rest nU nL nD nS → CountClasses (c :: rest) nU.succ nL nD nS
| lower : Lower c → CountClasses rest nU nL nD nS → CountClasses (c :: rest) nU nL.succ nD nS
| digit : Digit c → CountClasses rest nU nL nD nS → CountClasses (c :: rest) nU nL nD.succ nS
| symbol : Symbol c → CountClasses rest nU nL nD nS → CountClasses (c :: rest) nU nL nD nS.succ

/-! ## GEq: relational "greater than or equal" on Nat -/

inductive GEq : Nat → Nat → Prop where
| refl : GEq n n
| step : GEq n m → GEq n.succ m

/-! ## Between: value is in a closed range [lo, hi]

`Between n lo hi` holds iff `lo ≤ n ≤ hi`. Expressed inductively:
- `base`: n = lo (start of range, hi must be ≥ lo)
- `step`: if n is in [lo, hi-1], then n+1 is in [lo, hi]
-/

inductive Between : Nat → Nat → Nat → Prop where
| base : GEq hi lo → Between lo lo hi
| step : Between n lo hi → Between n.succ lo hi.succ

/-! ## Sum4: relational decomposition of a Nat into 4 non-negative parts -/

inductive Sum4 : Nat → Nat → Nat → Nat → Nat → Prop where
| zero : Sum4 .zero .zero .zero .zero .zero
| addU : Sum4 nU nL nD nS len → Sum4 nU.succ nL nD nS len.succ
| addL : Sum4 nU nL nD nS len → Sum4 nU nL.succ nD nS len.succ
| addD : Sum4 nU nL nD nS len → Sum4 nU nL nD.succ nS len.succ
| addS : Sum4 nU nL nD nS len → Sum4 nU nL nD nS.succ len.succ

/-! ## AddEq: relational addition (a + b = c) -/

inductive AddEq : Nat → Nat → Nat → Prop where
| zero : AddEq .zero b b
| succ : AddEq a b c → AddEq a.succ b c.succ

/-! ## ValidPassword: enforces AWS IAM minimums via CountClasses

`ValidPassword cs minU minL minD minS` holds iff `cs` has at least `minU` upper,
`minL` lower, `minD` digit, and `minS` symbol characters.
-/

inductive ValidPassword : List Char → Nat → Nat → Nat → Nat → Prop where
| mk : CountClasses cs nU nL nD nS →
       GEq nU minU →
       GEq nL minL →
       GEq nD minD →
       GEq nS minS →
       ValidPassword cs minU minL minD minS

/-! ## AtLeast3Positive: at least 3 of 4 Nats are positive (as a decidable Prop) -/

def atLeast3Positive (a b c d : Nat) : Bool :=
  (decide (a > 0) && decide (b > 0) && decide (c > 0)) ||
  (decide (a > 0) && decide (b > 0) && decide (d > 0)) ||
  (decide (a > 0) && decide (c > 0) && decide (d > 0)) ||
  (decide (b > 0) && decide (c > 0) && decide (d > 0))

/-! ## AWSPassword: full AWS IAM policy

Given `len` (total length) and per-class minimums, generates a password where:
- Total length = len
- len ∈ [8, 128]
- Each class count ≥ its minimum
- At least 3 of the 4 character classes are represented
- The excess (len - minSum) is distributed among the 4 classes via Sum4
-/

inductive AWSPassword : List Char → Nat → Nat → Nat → Nat → Nat → Prop where
| mk : Between len 8 128 →
       minSum = minU + minL + minD + minS →
       AddEq minSum excess len →
       Sum4 eU eL eD eS excess →
       nU = minU + eU → nL = minL + eL → nD = minD + eD → nS = minS + eS →
       atLeast3Positive nU nL nD nS = true →
       CountClasses cs nU nL nD nS →
       AWSPassword cs len minU minL minD minS

/-! ## Derive generator and checker -/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

instance {m : Nat} : ArbitrarySizedSuchThat Nat (fun n => GEq n m) where
  arbitrarySizedST s := do
    let extra ← Gen.choose Nat 0 (min 5 s) (by omega)
    return m + extra.val

instance {n m : Nat} : DecOpt (GEq n m) where
  decOpt _ := return decide (n ≥ m)

instance {lo hi : Nat} : ArbitrarySizedSuchThat Nat (fun n => Between n lo hi) where
  arbitrarySizedST _ := do
    if h : lo ≤ hi then
      let n ← Gen.choose Nat lo hi h
      return n.val
    else
      throw (.genError "Between: lo > hi")

instance {n lo hi : Nat} : DecOpt (Between n lo hi) where
  decOpt _ := return decide (lo ≤ n && n ≤ hi)

instance {a b c : Nat} : DecOpt (AddEq a b c) where
  decOpt _ := return decide (a + b = c)

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#time derive_mutual
  (fun nU nL nD nS => ∃ cs, CountClasses cs nU nL nD nS),
  (fun cs => ∃ nU nL nD nS, CountClasses cs nU nL nD nS),
  enumerator (fun cs => ∃ nU nL nD nS, CountClasses cs nU nL nD nS),
  checker (fun cs nU nL nD nS => CountClasses cs nU nL nD nS),
  (fun e => ∃ a b c d, Sum4 a b c d e),
  (fun minU minL minD minS => ∃ cs, ValidPassword cs minU minL minD minS),
  checker (fun cs minU minL minD minS => ValidPassword cs minU minL minD minS),
  (fun len minU minL minD minS => ∃ cs, AWSPassword cs len minU minL minD minS),
  checker (fun cs len minU minL minD minS => AWSPassword cs len minU minL minD minS),
  (fun minU minL minD minS => ∃ cs len, AWSPassword cs len minU minL minD minS)

/-! ## Sampling -/

#time #eval! do
  IO.println "=== AWS IAM Password Policy ==="

  IO.println "\n— Generator (exact counts → password) —"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun cs => CountClasses cs 3 3 2 0) 500) 500 with
  | .ok cs => IO.println s!"  [3U,3L,2D,0S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [3U,3L,2D,0S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [3U,3L,2D,0S]: impossible: {msg}"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun cs => CountClasses cs 2 2 2 2) 500) 500 with
  | .ok cs => IO.println s!"  [2U,2L,2D,2S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [2U,2L,2D,2S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [2U,2L,2D,2S]: impossible: {msg}"

  IO.println "\n— Generator (exact length + minimums) —"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun cs => AWSPassword cs 8 1 1 1 0) 500) 500 with
  | .ok cs => IO.println s!"  [len=8, ≥1U,≥1L,≥1D,≥0S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [len=8, ≥1U,≥1L,≥1D,≥0S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [len=8, ≥1U,≥1L,≥1D,≥0S]: impossible: {msg}"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun cs => AWSPassword cs 12 2 2 2 2) 500) 500 with
  | .ok cs => IO.println s!"  [len=12,≥2U,≥2L,≥2D,≥2S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [len=12,≥2U,≥2L,≥2D,≥2S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [len=12,≥2U,≥2L,≥2D,≥2S]: impossible: {msg}"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun cs => AWSPassword cs 16 1 1 1 1) 500) 500 with
  | .ok cs => IO.println s!"  [len=16,≥1U,≥1L,≥1D,≥1S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [len=16,≥1U,≥1L,≥1D,≥1S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [len=16,≥1U,≥1L,≥1D,≥1S]: impossible: {msg}"

  IO.println "\n— Generator (arbitrary length, AWS default policy) —"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun (cs, len) => AWSPassword cs len 1 1 0 0) 500) 500 with
  | .ok (cs, _) => IO.println s!"  [≥1U,≥1L,≥0D,≥0S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [≥1U,≥1L,≥0D,≥0S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [≥1U,≥1L,≥0D,≥0S]: impossible: {msg}"
  match ← Gen.runChecked (ArbitrarySizedSuchThat.arbitrarySizedST (fun (cs, len) => AWSPassword cs len 1 1 1 1) 500) 500 with
  | .ok (cs, _) => IO.println s!"  [≥1U,≥1L,≥1D,≥1S]: {String.ofList cs} (len={cs.length})"
  | .insufficientFuel msg => IO.println s!"  [≥1U,≥1L,≥1D,≥1S]: insufficient fuel: {msg}"
  | .impossible msg => IO.println s!"  [≥1U,≥1L,≥1D,≥1S]: impossible: {msg}"

  -- IO.println "\n— Checker (password → valid?) —"
  -- let check := fun (s : String) (len minU minL minD minS : Nat) =>
  --   DecOpt.decOpt (AWSPassword s.toList len minU minL minD minS) 100
  -- IO.println s!"  'Ab1Cd2Ef' [len=8,≥1U,≥1L,≥1D,≥0S]: {repr (check "Ab1Cd2Ef" 8 1 1 1 0)}"
  -- IO.println s!"  'AAAA1111' [len=8,≥1U,≥1L,≥1D,≥0S]: {repr (check "AAAA1111" 8 1 1 1 0)}"
  -- IO.println s!"  'Ab!1cD@2' [len=8,≥2U,≥2L,≥2D,≥2S]: {repr (check "Ab!1cD@2" 8 2 2 2 2)}"
  -- IO.println s!"  'Ab1' [len=3,≥1U,≥1L,≥1D,≥0S]: {repr (check "Ab1" 3 1 1 1 0)}"

end Password
