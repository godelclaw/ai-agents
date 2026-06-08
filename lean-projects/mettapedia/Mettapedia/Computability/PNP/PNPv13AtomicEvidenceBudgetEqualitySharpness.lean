import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetCancellationObstruction
import Mathlib.Tactic

/-!
# PNP v13 atomic evidence budget equality sharpness

The previous atomic-budget files show:

- over-budget sums expose double-counted positive-cost atoms;
- under-budget sums expose missed positive-cost atoms;
- exact budget equality does not by itself force either side condition.

This file isolates the exact sharpness boundary.  If one side condition is known,
then budget equality forces the other.  Equivalently, on the equality surface,
`NoDoubleCounting` and `AllPositiveCostAtomsCharged` are the same obligation.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace V13AtomicEvidenceBudgetSurface

/-- If no positive-cost atom is double-counted but some positive-cost atom is
missed, the coordinate-summed cost is strictly below the once-per-atom budget. -/
theorem coordinateSummedCost_lt_atomBudget_of_noDoubleCounting_of_missedPositiveCostAtom
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) (hmiss : S.MissedPositiveCostAtom) :
    S.coordinateSummedCost < S.atomBudget := by
  classical
  rcases hmiss with ⟨a, hcost, hmult⟩
  have ha_mem : a ∈ (Finset.univ : Finset Atom) := by simp
  let restCoord : Nat :=
    (Finset.univ.erase a).sum fun b => S.atomMultiplicity b * S.atomCost b
  let restBudget : Nat :=
    (Finset.univ.erase a).sum fun b => S.atomCost b
  have hrest : restCoord ≤ restBudget := by
    dsimp [restCoord, restBudget]
    refine Finset.sum_le_sum ?_
    intro b hb
    by_cases hbcost : 0 < S.atomCost b
    · have hmul :
          S.atomMultiplicity b * S.atomCost b ≤ 1 * S.atomCost b :=
        Nat.mul_le_mul_right (S.atomCost b) (hno b hbcost)
      simpa using hmul
    · have hzero : S.atomCost b = 0 := by omega
      simp [hzero]
  calc
    S.coordinateSummedCost =
        restCoord +
          S.atomMultiplicity a * S.atomCost a := by
          dsimp [restCoord]
          rw [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
            ← Finset.sum_erase_add (a := a) (s := (Finset.univ : Finset Atom))
              (f := fun b => S.atomMultiplicity b * S.atomCost b) ha_mem]
    _ = restCoord := by
          simp [hmult]
    _ ≤ restBudget := hrest
    _ < restBudget + S.atomCost a := by
          dsimp [restBudget]
          exact Nat.lt_add_of_pos_right hcost
    _ = S.atomBudget := by
          dsimp [restBudget]
          rw [V13AtomicEvidenceBudgetSurface.atomBudget,
            ← Finset.sum_erase_add (a := a) (s := (Finset.univ : Finset Atom))
              (f := fun b => S.atomCost b) ha_mem]

/-- If every positive-cost atom is charged at least once but some positive-cost
atom is double-counted, the coordinate-summed cost is strictly above the
once-per-atom budget. -/
theorem atomBudget_lt_coordinateSummedCost_of_allPositiveCostAtomsCharged_of_doubleCountedAtom
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hall : S.AllPositiveCostAtomsCharged) (hdouble : S.DoubleCountedAtom) :
    S.atomBudget < S.coordinateSummedCost := by
  classical
  rcases hdouble with ⟨a, hcost, hmult⟩
  have ha_mem : a ∈ (Finset.univ : Finset Atom) := by simp
  let restBudget : Nat :=
    (Finset.univ.erase a).sum fun b => S.atomCost b
  let restCoord : Nat :=
    (Finset.univ.erase a).sum fun b => S.atomMultiplicity b * S.atomCost b
  have hrest : restBudget ≤ restCoord := by
    dsimp [restBudget, restCoord]
    refine Finset.sum_le_sum ?_
    intro b hb
    by_cases hbcost : 0 < S.atomCost b
    · have hmul :
          1 * S.atomCost b ≤ S.atomMultiplicity b * S.atomCost b :=
        Nat.mul_le_mul_right (S.atomCost b) (hall b hbcost)
      simpa using hmul
    · have hzero : S.atomCost b = 0 := by omega
      simp [hzero]
  have hstrict :
      S.atomCost a < S.atomMultiplicity a * S.atomCost a := by
    simpa using Nat.mul_lt_mul_of_pos_right hmult hcost
  calc
    S.atomBudget = restBudget + S.atomCost a := by
      dsimp [restBudget]
      rw [V13AtomicEvidenceBudgetSurface.atomBudget,
        ← Finset.sum_erase_add (a := a) (s := (Finset.univ : Finset Atom))
          (f := fun b => S.atomCost b) ha_mem]
    _ < restCoord +
          S.atomMultiplicity a * S.atomCost a := by
            exact Nat.add_lt_add_of_le_of_lt hrest hstrict
    _ = S.coordinateSummedCost := by
      dsimp [restCoord]
      rw [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
        ← Finset.sum_erase_add (a := a) (s := (Finset.univ : Finset Atom))
          (f := fun b => S.atomMultiplicity b * S.atomCost b) ha_mem]

/-- On the exact budget surface, no-double-counting already forces every
positive-cost atom to be charged. -/
theorem allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget_of_noDoubleCounting
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) (hno : S.NoDoubleCounting) :
    S.AllPositiveCostAtomsCharged := by
  by_contra hall
  have hmiss : S.MissedPositiveCostAtom := by
    by_contra hnotmiss
    exact hall ((S.allPositiveCostAtomsCharged_iff_not_missedPositiveCostAtom).2 hnotmiss)
  have hlt : S.coordinateSummedCost < S.atomBudget :=
    S.coordinateSummedCost_lt_atomBudget_of_noDoubleCounting_of_missedPositiveCostAtom
      hno hmiss
  omega

/-- On the exact budget surface, charging every positive-cost atom already
forces no-double-counting. -/
theorem noDoubleCounting_of_coordinateSummedCost_eq_atomBudget_of_allPositiveCostAtomsCharged
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget)
    (hall : S.AllPositiveCostAtomsCharged) :
    S.NoDoubleCounting := by
  have hnot : ¬ S.DoubleCountedAtom := by
    intro hdouble
    have hlt : S.atomBudget < S.coordinateSummedCost :=
      S.atomBudget_lt_coordinateSummedCost_of_allPositiveCostAtomsCharged_of_doubleCountedAtom
        hall hdouble
    omega
  exact (S.noDoubleCounting_iff_not_doubleCountedAtom).2 hnot

/-- Exact budget equality makes the two structural side conditions equivalent. -/
theorem noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged := by
  constructor
  · intro hno
    exact S.allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget_of_noDoubleCounting
      heq hno
  · intro hall
    exact S.noDoubleCounting_of_coordinateSummedCost_eq_atomBudget_of_allPositiveCostAtomsCharged
      heq hall

end V13AtomicEvidenceBudgetSurface

end Mettapedia.Computability.PNP
