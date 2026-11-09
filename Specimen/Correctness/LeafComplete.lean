import Specimen.Correctness.ReachClose
import Specimen.Correctness.SearchFinds

/-!
# The unconstrained generators of the base types are complete

`ArbitrarySizedComplete` for `Bool`, `Unit`, `Int`, `Char`, `String`, and `Option`, `×` and `⊕` of
complete types (`Nat` and `List` are in `ReachClose`). The generators derived for a user's types draw
from these.
-/

namespace Specimen.Correctness

open Basalt

instance : ArbitrarySizedComplete Bool where
  complete b := ⟨0, fun s _ => produces_of_reach (by
    show reachObs.spec (do pure ((← chooseNat 0 1) == 0) : SGen Bool) _
    walk
    cases b
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩)⟩

instance : ArbitrarySizedComplete Unit where
  complete _ := ⟨0, fun _ _ => produces_pure_iff.mpr rfl⟩

instance : ArbitrarySizedComplete Int where
  complete i := ⟨i.natAbs, fun s hs => by
    show Produces (do pure ((← chooseNat 0 (2 * s) : Nat) - (s : Int)) : SGen Int) i
    refine produces_bind_of (produces_chooseNat (k := (i + s).toNat) _ (Nat.zero_le _) (by omega))
      (produces_pure_iff.mpr ?_)
    omega⟩

instance : ArbitrarySizedComplete Char where
  complete c := ⟨0, fun s _ => by
    show Produces (frequency [(19, fun _ => do pure (Char.ofNat (← chooseNat 32 126))),
      (1, fun _ => do pure (Char.ofNat (← chooseNat 0 0x10FFFF)))] : SGen Char) c
    refine produces_of_reach ((reach_frequency (by decide)).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      by decide, reach_of_produces ?_⟩)
    have hc : c.toNat ≤ 0x10FFFF := by
      have h := c.valid
      simp only [Char.toNat, UInt32.isValidChar, Nat.isValidChar] at *
      omega
    exact produces_bind_of (produces_chooseNat (k := c.toNat) _ (Nat.zero_le _) hc)
      (produces_pure_iff.mpr (Char.ofNat_toNat c).symm)⟩

instance {α : Type} [ArbitrarySized α] [ArbitrarySizedComplete α] : ArbitrarySizedComplete (Option α) where
  complete o := ⟨match o with | none => 0 | some a => ArbitrarySizedComplete.bound a, fun s hs => by
    refine produces_of_reach ?_
    show reachObs.spec (oneOf [fun () => pure none, fun () => some <$> ArbitrarySized.arbitrarySized s] :
      SGen (Option α)) _
    walk
    cases o with
    | none => exact Or.inl rfl
    | some a => exact Or.inr ⟨a, ArbitrarySizedComplete.produces hs, rfl⟩⟩

instance {α β : Type} [ArbitrarySized α] [ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] : ArbitrarySizedComplete (α × β) where
  complete p := ⟨ArbitrarySizedComplete.bound p.1 + ArbitrarySizedComplete.bound p.2, fun s hs => by
    show Produces (do
      let a ← ArbitrarySized.arbitrarySized s
      let b ← ArbitrarySized.arbitrarySized s
      pure (a, b) : SGen (α × β)) p
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := p.1) (by omega))
      (produces_bind_of (ArbitrarySizedComplete.produces (x := p.2) (by omega))
        (produces_pure_iff.mpr rfl))⟩

instance {α β : Type} [ArbitrarySized α] [ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] : ArbitrarySizedComplete (α ⊕ β) where
  complete p := ⟨Sum.elim ArbitrarySizedComplete.bound ArbitrarySizedComplete.bound p, fun s hs => by
    refine produces_of_reach ?_
    show reachObs.spec (oneOf [fun () => Sum.inl <$> ArbitrarySized.arbitrarySized s,
      fun () => Sum.inr <$> ArbitrarySized.arbitrarySized s] : SGen (α ⊕ β)) _
    walk
    cases p with
    | inl a => exact Or.inl ⟨a, ArbitrarySizedComplete.produces hs, rfl⟩
    | inr b => exact Or.inr ⟨b, ArbitrarySizedComplete.produces hs, rfl⟩⟩

instance : ArbitrarySizedComplete String where
  complete str := ⟨ArbitrarySizedComplete.bound str.toList, fun s hs => by
    show Produces (do pure (String.ofList (← ArbitrarySized.arbitrarySized (α := List Char) s)) :
      SGen String) str
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := str.toList) hs)
      (produces_pure_iff.mpr String.ofList_toList.symm)⟩

/-- `ArbitrarySizedComplete` for a type whose generator was derived (`deriving instance
Basalt.ArbitrarySized`): for each constructor, the walk of the generator at a positive size, its
choices made by `reach_close` from the fields' own `ArbitrarySizedComplete` instances, the size bound
their sum. Use as `⟨by arbitrary_complete⟩`. -/
macro "arbitrary_complete" : tactic => `(tactic| (
  intro x
  cases x <;>
  (refine ⟨?_ + 1, fun s hs => produces_of_reach ?_⟩
   on_goal 2 => (
     cases s with
     | zero => exact absurd hs (Nat.not_succ_le_zero _)
     | succ s =>
       have hs := Nat.le_of_succ_le_succ hs
       unfold_arbitrary; walk; all_goals reach_close; reach_close_bounds)
   all_goals exact 0)))

end Specimen.Correctness
