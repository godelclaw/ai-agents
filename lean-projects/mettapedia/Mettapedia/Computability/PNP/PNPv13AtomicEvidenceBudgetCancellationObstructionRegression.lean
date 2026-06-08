import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetCancellationObstruction

/-!
# Regression checks for the PNP v13 atomic evidence budget cancellation obstruction
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetCancellationObstructionRegression

open Mettapedia.Computability.PNP

theorem cancellation_budget_surface_exact_budget_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
      v13CancellationBudgetSurface.atomBudget := by
  exact v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem cancellation_budget_surface_double_counted_atom_regression :
    v13CancellationBudgetSurface.DoubleCountedAtom := by
  exact v13CancellationBudgetSurface_doubleCountedAtom

theorem cancellation_budget_surface_missed_positive_cost_atom_regression :
    v13CancellationBudgetSurface.MissedPositiveCostAtom := by
  exact v13CancellationBudgetSurface_missedPositiveCostAtom

theorem cancellation_budget_surface_blocks_no_double_counting_regression :
    ¬ v13CancellationBudgetSurface.NoDoubleCounting := by
  exact v13CancellationBudgetSurface_not_noDoubleCounting

theorem cancellation_budget_surface_blocks_all_positive_cost_atoms_charged_regression :
    ¬ v13CancellationBudgetSurface.AllPositiveCostAtomsCharged := by
  exact v13CancellationBudgetSurface_not_allPositiveCostAtomsCharged

theorem cancellation_budget_surface_exact_budget_with_double_count_and_omission_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      v13CancellationBudgetSurface.DoubleCountedAtom ∧
      v13CancellationBudgetSurface.MissedPositiveCostAtom := by
  exact v13CancellationBudgetSurface_exact_budget_with_double_count_and_omission

theorem exact_budget_does_not_force_no_double_counting_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget → S.NoDoubleCounting := by
  exact not_forall_coordinateSummedCost_eq_atomBudget_implies_noDoubleCounting

theorem exact_budget_does_not_force_all_positive_cost_atoms_charged_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget → S.AllPositiveCostAtomsCharged := by
  exact not_forall_coordinateSummedCost_eq_atomBudget_implies_allPositiveCostAtomsCharged

theorem exact_budget_does_not_force_exactness_side_conditions_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          S.NoDoubleCounting ∧ S.AllPositiveCostAtomsCharged := by
  exact not_forall_coordinateSummedCost_eq_atomBudget_implies_exactness_side_conditions

end Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetCancellationObstructionRegression
