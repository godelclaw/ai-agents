import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessCharacterization
import Mathlib.Tactic

/-!
# PNP v13 atomic evidence budget cancellation obstruction

The previous atomic-budget files isolate the two one-sided failures separately:
double counting can make the coordinate-summed cost exceed the once-per-atom
budget, and omission can make it fall below.  This file blocks the next repair
escape: aggregate budget equality does not certify either side condition.  A
single double-counted positive-cost atom can be canceled by a different omitted
positive-cost atom, leaving exact equality while both structural failures remain.
-/

namespace Mettapedia.Computability.PNP

/-- Cancellation toy surface: both coordinates charge atom `0`, while atom `1`
is never charged.  Both atoms have unit cost, so the exact budget balance hides
one double-counted and one omitted positive-cost atom. -/
def v13CancellationBudgetSurface :
    V13AtomicEvidenceBudgetSurface (Fin 2) (Fin 2) where
  charges := fun _ a => a = 0
  atomCost := fun _ => 1

instance v13CancellationBudgetSurface_decidableRel :
    DecidableRel v13CancellationBudgetSurface.charges := by
  intro c a
  dsimp [v13CancellationBudgetSurface]
  infer_instance

theorem v13CancellationBudgetSurface_atomMultiplicity_zero :
    v13CancellationBudgetSurface.atomMultiplicity 0 = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13CancellationBudgetSurface]

theorem v13CancellationBudgetSurface_atomMultiplicity_one :
    v13CancellationBudgetSurface.atomMultiplicity 1 = 0 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13CancellationBudgetSurface]

theorem v13CancellationBudgetSurface_atomBudget :
    v13CancellationBudgetSurface.atomBudget = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomBudget, v13CancellationBudgetSurface]

theorem v13CancellationBudgetSurface_coordinateSummedCost :
    v13CancellationBudgetSurface.coordinateSummedCost = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
    V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13CancellationBudgetSurface]

theorem v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget :
    v13CancellationBudgetSurface.coordinateSummedCost =
      v13CancellationBudgetSurface.atomBudget := by
  rw [v13CancellationBudgetSurface_coordinateSummedCost,
    v13CancellationBudgetSurface_atomBudget]

theorem v13CancellationBudgetSurface_doubleCountedAtom :
    v13CancellationBudgetSurface.DoubleCountedAtom := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [v13CancellationBudgetSurface]
  · rw [v13CancellationBudgetSurface_atomMultiplicity_zero]
    omega

theorem v13CancellationBudgetSurface_missedPositiveCostAtom :
    v13CancellationBudgetSurface.MissedPositiveCostAtom := by
  refine ⟨1, ?_, ?_⟩
  · norm_num [v13CancellationBudgetSurface]
  · exact v13CancellationBudgetSurface_atomMultiplicity_one

theorem v13CancellationBudgetSurface_not_noDoubleCounting :
    ¬ v13CancellationBudgetSurface.NoDoubleCounting := by
  intro hno
  have hle : v13CancellationBudgetSurface.atomMultiplicity 0 ≤ 1 :=
    hno 0 (by norm_num [v13CancellationBudgetSurface])
  rw [v13CancellationBudgetSurface_atomMultiplicity_zero] at hle
  omega

theorem v13CancellationBudgetSurface_not_allPositiveCostAtomsCharged :
    ¬ v13CancellationBudgetSurface.AllPositiveCostAtomsCharged := by
  intro hall
  have hcharged : 1 ≤ v13CancellationBudgetSurface.atomMultiplicity 1 :=
    hall 1 (by norm_num [v13CancellationBudgetSurface])
  rw [v13CancellationBudgetSurface_atomMultiplicity_one] at hcharged
  omega

/-- Concrete route anchor: exact budget equality can coexist with both a
double-counted and an omitted positive-cost atom. -/
theorem v13CancellationBudgetSurface_exact_budget_with_double_count_and_omission :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      v13CancellationBudgetSurface.DoubleCountedAtom ∧
      v13CancellationBudgetSurface.MissedPositiveCostAtom := by
  exact
    ⟨v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget,
      v13CancellationBudgetSurface_doubleCountedAtom,
      v13CancellationBudgetSurface_missedPositiveCostAtom⟩

/-- Aggregate budget equality alone does not force no-double-counting. -/
theorem not_forall_coordinateSummedCost_eq_atomBudget_implies_noDoubleCounting :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget → S.NoDoubleCounting := by
  intro hall
  have hno : v13CancellationBudgetSurface.NoDoubleCounting :=
    hall (S := v13CancellationBudgetSurface)
      v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget
  exact v13CancellationBudgetSurface_not_noDoubleCounting hno

/-- Aggregate budget equality alone does not force every positive-cost atom to
be charged. -/
theorem not_forall_coordinateSummedCost_eq_atomBudget_implies_allPositiveCostAtomsCharged :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget → S.AllPositiveCostAtomsCharged := by
  intro hall
  have hall' : v13CancellationBudgetSurface.AllPositiveCostAtomsCharged :=
    hall (S := v13CancellationBudgetSurface)
      v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget
  exact v13CancellationBudgetSurface_not_allPositiveCostAtomsCharged hall'

/-- Aggregate budget equality alone does not force the conjunction of the two
exactness side conditions either. -/
theorem not_forall_coordinateSummedCost_eq_atomBudget_implies_exactness_side_conditions :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          S.NoDoubleCounting ∧ S.AllPositiveCostAtomsCharged := by
  intro hall
  have hpair :
      v13CancellationBudgetSurface.NoDoubleCounting ∧
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged :=
    hall (S := v13CancellationBudgetSurface)
      v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget
  exact v13CancellationBudgetSurface_not_noDoubleCounting hpair.1

end Mettapedia.Computability.PNP
