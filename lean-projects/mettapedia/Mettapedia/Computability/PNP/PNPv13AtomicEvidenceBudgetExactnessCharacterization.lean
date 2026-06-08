import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudget
import Mathlib.Tactic

/-!
# PNP v13 atomic evidence budget exactness characterization

`PNPv13AtomicEvidenceBudget` isolates the manuscript's over-budget failure mode:
strictly exceeding the once-per-atom budget exposes a positive-cost atom charged
more than once.  This file supplies the missing dual obstruction.  If a
positive-cost atom is not charged at all, the coordinate-summed cost can fall
strictly below the once-per-atom budget.  Exact budget reuse therefore needs
both sides: no positive-cost double counting and no positive-cost omission.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace V13AtomicEvidenceBudgetSurface

/-- Every positive-cost atom is charged by at least one coordinate. -/
def AllPositiveCostAtomsCharged {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] : Prop :=
  ∀ a, 0 < S.atomCost a → 1 ≤ S.atomMultiplicity a

/-- A concrete omission witness: a positive-cost atom charged by no coordinate. -/
def MissedPositiveCostAtom {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] : Prop :=
  ∃ a, 0 < S.atomCost a ∧ S.atomMultiplicity a = 0

/-- Charging every positive-cost atom at least once is exactly the absence of a
positive-cost atom with multiplicity zero. -/
theorem allPositiveCostAtomsCharged_iff_not_missedPositiveCostAtom
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] :
    S.AllPositiveCostAtomsCharged ↔ ¬ S.MissedPositiveCostAtom := by
  constructor
  · intro hall hmiss
    rcases hmiss with ⟨a, hcost, hmult⟩
    have hcharged : 1 ≤ S.atomMultiplicity a := hall a hcost
    omega
  · intro hnot a hcost
    by_contra hcharged
    have hmult : S.atomMultiplicity a = 0 := by omega
    exact hnot ⟨a, hcost, hmult⟩

/-- If every positive-cost atom is charged at least once, then the once-per-atom
budget is bounded by the coordinate-summed cost. -/
theorem atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hall : S.AllPositiveCostAtomsCharged) :
    S.atomBudget ≤ S.coordinateSummedCost := by
  classical
  dsimp [atomBudget, coordinateSummedCost]
  refine Finset.sum_le_sum ?_
  intro a _ha
  by_cases hcost : 0 < S.atomCost a
  · have hmul : 1 ≤ S.atomMultiplicity a := hall a hcost
    have hle : 1 * S.atomCost a ≤ S.atomMultiplicity a * S.atomCost a :=
      Nat.mul_le_mul_right (S.atomCost a) hmul
    simpa using hle
  · have hzero : S.atomCost a = 0 := by omega
    simp [hzero]

/-- Any strict under-budget coordinate sum exposes a positive-cost atom that was
never charged by any coordinate. -/
theorem missedPositiveCostAtom_of_coordinateSummedCost_lt_atomBudget
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hlt : S.coordinateSummedCost < S.atomBudget) :
    S.MissedPositiveCostAtom := by
  by_contra hmiss
  have hall : S.AllPositiveCostAtomsCharged :=
    (S.allPositiveCostAtomsCharged_iff_not_missedPositiveCostAtom).2 hmiss
  have hle : S.atomBudget ≤ S.coordinateSummedCost :=
    S.atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged hall
  omega

/-- Exact reuse of the once-per-atom budget requires both no positive-cost
double counting and no positive-cost omission. -/
theorem coordinateSummedCost_eq_atomBudget_of_noDoubleCounting_of_allPositiveCostAtomsCharged
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) (hall : S.AllPositiveCostAtomsCharged) :
    S.coordinateSummedCost = S.atomBudget := by
  have hupper : S.coordinateSummedCost ≤ S.atomBudget :=
    S.coordinateSummedCost_le_atomBudget_of_noDoubleCounting hno
  have hlower : S.atomBudget ≤ S.coordinateSummedCost :=
    S.atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged hall
  exact Nat.le_antisymm hupper hlower

end V13AtomicEvidenceBudgetSurface

/-- Exact one-atom surface: the shared budget is paid once and charged once. -/
def v13ExactAtomicBudgetSurface :
    V13AtomicEvidenceBudgetSurface (Fin 1) (Fin 1) where
  charges := fun _ _ => True
  atomCost := fun _ => 1

instance v13ExactAtomicBudgetSurface_decidableRel :
    DecidableRel v13ExactAtomicBudgetSurface.charges :=
  fun _ _ => isTrue trivial

/-- Omission toy surface: one positive-cost atom is charged, one is missed. -/
def v13MissedPositiveBudgetSurface :
    V13AtomicEvidenceBudgetSurface (Fin 1) (Fin 2) where
  charges := fun _ a => a = 0
  atomCost := fun _ => 1

instance v13MissedPositiveBudgetSurface_decidableRel :
    DecidableRel v13MissedPositiveBudgetSurface.charges := by
  intro c a
  dsimp [v13MissedPositiveBudgetSurface]
  infer_instance

theorem v13ExactAtomicBudgetSurface_atomBudget :
    v13ExactAtomicBudgetSurface.atomBudget = 1 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomBudget, v13ExactAtomicBudgetSurface]

theorem v13ExactAtomicBudgetSurface_coordinateSummedCost :
    v13ExactAtomicBudgetSurface.coordinateSummedCost = 1 := by
  norm_num [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
    V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13ExactAtomicBudgetSurface]

theorem v13ExactAtomicBudgetSurface_noDoubleCounting :
    v13ExactAtomicBudgetSurface.NoDoubleCounting := by
  intro a hcost
  fin_cases a
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13ExactAtomicBudgetSurface]

theorem v13ExactAtomicBudgetSurface_allPositiveCostAtomsCharged :
    v13ExactAtomicBudgetSurface.AllPositiveCostAtomsCharged := by
  intro a hcost
  fin_cases a
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13ExactAtomicBudgetSurface]

theorem v13ExactAtomicBudgetSurface_coordinateSummedCost_eq_atomBudget :
    v13ExactAtomicBudgetSurface.coordinateSummedCost =
      v13ExactAtomicBudgetSurface.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_noDoubleCounting_of_allPositiveCostAtomsCharged
      v13ExactAtomicBudgetSurface
      v13ExactAtomicBudgetSurface_noDoubleCounting
      v13ExactAtomicBudgetSurface_allPositiveCostAtomsCharged

theorem v13MissedPositiveBudgetSurface_atomMultiplicity_zero :
    v13MissedPositiveBudgetSurface.atomMultiplicity 0 = 1 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13MissedPositiveBudgetSurface]

theorem v13MissedPositiveBudgetSurface_atomMultiplicity_one :
    v13MissedPositiveBudgetSurface.atomMultiplicity 1 = 0 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13MissedPositiveBudgetSurface]

theorem v13MissedPositiveBudgetSurface_atomBudget :
    v13MissedPositiveBudgetSurface.atomBudget = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomBudget, v13MissedPositiveBudgetSurface]

theorem v13MissedPositiveBudgetSurface_coordinateSummedCost :
    v13MissedPositiveBudgetSurface.coordinateSummedCost = 1 := by
  norm_num [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
    V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13MissedPositiveBudgetSurface]

theorem v13MissedPositiveBudgetSurface_missedPositiveCostAtom :
    v13MissedPositiveBudgetSurface.MissedPositiveCostAtom := by
  refine ⟨1, ?_, ?_⟩
  · norm_num [v13MissedPositiveBudgetSurface]
  · exact v13MissedPositiveBudgetSurface_atomMultiplicity_one

theorem v13MissedPositiveBudgetSurface_not_allPositiveCostAtomsCharged :
    ¬ v13MissedPositiveBudgetSurface.AllPositiveCostAtomsCharged := by
  intro hall
  have hcharged : 1 ≤ v13MissedPositiveBudgetSurface.atomMultiplicity 1 :=
    hall 1 (by norm_num [v13MissedPositiveBudgetSurface])
  rw [v13MissedPositiveBudgetSurface_atomMultiplicity_one] at hcharged
  omega

theorem v13MissedPositiveBudgetSurface_coordinateSummedCost_lt_atomBudget :
    v13MissedPositiveBudgetSurface.coordinateSummedCost <
      v13MissedPositiveBudgetSurface.atomBudget := by
  rw [v13MissedPositiveBudgetSurface_coordinateSummedCost,
    v13MissedPositiveBudgetSurface_atomBudget]
  norm_num

end Mettapedia.Computability.PNP
