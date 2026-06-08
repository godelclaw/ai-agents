import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReduction

/-!
# Regression checks for the PNP v13 atomic evidence budget exactness reduction
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReductionRegression

open Mettapedia.Computability.PNP

universe u v

theorem coordinate_summed_cost_eq_atom_budget_of_exactness_side_conditions_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hexact : S.ExactnessSideConditions) :
    S.coordinateSummedCost = S.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_exactnessSideConditions
      S hexact

theorem exactness_side_conditions_iff_no_double_counting_of_coordinate_summed_cost_eq_atom_budget_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.ExactnessSideConditions ↔ S.NoDoubleCounting := by
  exact
    V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_noDoubleCounting_of_coordinateSummedCost_eq_atomBudget
      S heq

theorem exactness_side_conditions_iff_all_positive_cost_atoms_charged_of_coordinate_summed_cost_eq_atom_budget_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.ExactnessSideConditions ↔ S.AllPositiveCostAtomsCharged := by
  exact
    V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
      S heq

theorem exact_atomic_budget_surface_exactness_side_conditions :
    v13ExactAtomicBudgetSurface.ExactnessSideConditions := by
  exact
    ⟨v13ExactAtomicBudgetSurface_noDoubleCounting,
      v13ExactAtomicBudgetSurface_allPositiveCostAtomsCharged⟩

theorem exact_atomic_budget_surface_exactness_reuses_budget_regression :
    v13ExactAtomicBudgetSurface.coordinateSummedCost =
      v13ExactAtomicBudgetSurface.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_exactnessSideConditions
      v13ExactAtomicBudgetSurface
      exact_atomic_budget_surface_exactness_side_conditions

theorem exact_atomic_budget_surface_exactness_iff_no_double_counting_regression :
    v13ExactAtomicBudgetSurface.ExactnessSideConditions ↔
      v13ExactAtomicBudgetSurface.NoDoubleCounting := by
  exact
    V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_noDoubleCounting_of_coordinateSummedCost_eq_atomBudget
      v13ExactAtomicBudgetSurface
      v13ExactAtomicBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem exact_atomic_budget_surface_exactness_iff_all_positive_cost_atoms_charged_regression :
    v13ExactAtomicBudgetSurface.ExactnessSideConditions ↔
      v13ExactAtomicBudgetSurface.AllPositiveCostAtomsCharged := by
  exact
    V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
      v13ExactAtomicBudgetSurface
      v13ExactAtomicBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem cancellation_budget_surface_exact_budget_with_side_condition_equivalence_without_exactness_side_conditions_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  exact
    v13CancellationBudgetSurface_exact_budget_with_sideConditionEquivalence_without_exactnessSideConditions

theorem not_forall_coordinate_summed_cost_eq_atom_budget_and_side_condition_equivalence_implies_exactness_side_conditions_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
          S.ExactnessSideConditions := by
  exact
    not_forall_coordinateSummedCost_eq_atomBudget_and_sideConditionEquivalence_implies_exactnessSideConditions

end Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReductionRegression
