import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessCharacterization

/-!
# Regression checks for the PNP v13 atomic evidence budget exactness boundary
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessCharacterizationRegression

open Mettapedia.Computability.PNP

universe u v

theorem all_positive_cost_atoms_charged_iff_not_missed_positive_cost_atom_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] :
    S.AllPositiveCostAtomsCharged ↔ ¬ S.MissedPositiveCostAtom := by
  exact
    V13AtomicEvidenceBudgetSurface.allPositiveCostAtomsCharged_iff_not_missedPositiveCostAtom
      S

theorem atom_budget_le_coordinate_summed_cost_of_all_positive_cost_atoms_charged_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hall : S.AllPositiveCostAtomsCharged) :
    S.atomBudget ≤ S.coordinateSummedCost := by
  exact
    V13AtomicEvidenceBudgetSurface.atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged
      S hall

theorem missed_positive_cost_atom_of_coordinate_summed_cost_lt_atom_budget_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hlt : S.coordinateSummedCost < S.atomBudget) :
    S.MissedPositiveCostAtom := by
  exact
    V13AtomicEvidenceBudgetSurface.missedPositiveCostAtom_of_coordinateSummedCost_lt_atomBudget
      S hlt

theorem coordinate_summed_cost_eq_atom_budget_of_no_double_counting_of_all_positive_cost_atoms_charged_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) (hall : S.AllPositiveCostAtomsCharged) :
    S.coordinateSummedCost = S.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_noDoubleCounting_of_allPositiveCostAtomsCharged
      S hno hall

theorem exact_atomic_budget_surface_atom_budget_regression :
    v13ExactAtomicBudgetSurface.atomBudget = 1 := by
  exact v13ExactAtomicBudgetSurface_atomBudget

theorem exact_atomic_budget_surface_coordinate_summed_cost_regression :
    v13ExactAtomicBudgetSurface.coordinateSummedCost = 1 := by
  exact v13ExactAtomicBudgetSurface_coordinateSummedCost

theorem exact_atomic_budget_surface_exactness_regression :
    v13ExactAtomicBudgetSurface.coordinateSummedCost =
      v13ExactAtomicBudgetSurface.atomBudget := by
  exact v13ExactAtomicBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem missed_positive_budget_surface_atom_budget_regression :
    v13MissedPositiveBudgetSurface.atomBudget = 2 := by
  exact v13MissedPositiveBudgetSurface_atomBudget

theorem missed_positive_budget_surface_coordinate_summed_cost_regression :
    v13MissedPositiveBudgetSurface.coordinateSummedCost = 1 := by
  exact v13MissedPositiveBudgetSurface_coordinateSummedCost

theorem missed_positive_budget_surface_under_budget_regression :
    v13MissedPositiveBudgetSurface.coordinateSummedCost <
      v13MissedPositiveBudgetSurface.atomBudget := by
  exact v13MissedPositiveBudgetSurface_coordinateSummedCost_lt_atomBudget

theorem missed_positive_budget_surface_exposes_missed_positive_cost_atom_regression :
    v13MissedPositiveBudgetSurface.MissedPositiveCostAtom := by
  exact v13MissedPositiveBudgetSurface_missedPositiveCostAtom

theorem missed_positive_budget_surface_blocks_all_positive_cost_atoms_charged_regression :
    ¬ v13MissedPositiveBudgetSurface.AllPositiveCostAtomsCharged := by
  exact v13MissedPositiveBudgetSurface_not_allPositiveCostAtomsCharged

end Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessCharacterizationRegression
