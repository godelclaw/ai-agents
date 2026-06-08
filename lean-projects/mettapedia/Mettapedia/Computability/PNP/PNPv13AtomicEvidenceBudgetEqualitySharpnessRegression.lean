import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetEqualitySharpness

/-!
# Regression checks for the PNP v13 atomic evidence budget equality sharpness
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetEqualitySharpnessRegression

open Mettapedia.Computability.PNP

universe u v

theorem coordinate_summed_cost_lt_atom_budget_of_no_double_counting_of_missed_positive_cost_atom_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) (hmiss : S.MissedPositiveCostAtom) :
    S.coordinateSummedCost < S.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_lt_atomBudget_of_noDoubleCounting_of_missedPositiveCostAtom
      S hno hmiss

theorem atom_budget_lt_coordinate_summed_cost_of_all_positive_cost_atoms_charged_of_double_counted_atom_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hall : S.AllPositiveCostAtomsCharged) (hdouble : S.DoubleCountedAtom) :
    S.atomBudget < S.coordinateSummedCost := by
  exact
    V13AtomicEvidenceBudgetSurface.atomBudget_lt_coordinateSummedCost_of_allPositiveCostAtomsCharged_of_doubleCountedAtom
      S hall hdouble

theorem no_double_counting_iff_all_positive_cost_atoms_charged_of_coordinate_summed_cost_eq_atom_budget_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged := by
  exact
    V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
      S heq

theorem v13_missed_positive_budget_surface_no_double_counting :
    v13MissedPositiveBudgetSurface.NoDoubleCounting := by
  intro a hcost
  fin_cases a <;>
    norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13MissedPositiveBudgetSurface]

theorem v13_double_counted_budget_surface_all_positive_cost_atoms_charged :
    v13DoubleCountedBudgetSurface.AllPositiveCostAtomsCharged := by
  intro a hcost
  fin_cases a
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity, v13DoubleCountedBudgetSurface]

theorem missed_positive_budget_surface_strict_under_budget_regression :
    v13MissedPositiveBudgetSurface.coordinateSummedCost <
      v13MissedPositiveBudgetSurface.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_lt_atomBudget_of_noDoubleCounting_of_missedPositiveCostAtom
      v13MissedPositiveBudgetSurface
      v13_missed_positive_budget_surface_no_double_counting
      v13MissedPositiveBudgetSurface_missedPositiveCostAtom

theorem double_counted_budget_surface_strict_over_budget_regression :
    v13DoubleCountedBudgetSurface.atomBudget <
      v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact
    V13AtomicEvidenceBudgetSurface.atomBudget_lt_coordinateSummedCost_of_allPositiveCostAtomsCharged_of_doubleCountedAtom
      v13DoubleCountedBudgetSurface
      v13_double_counted_budget_surface_all_positive_cost_atoms_charged
      v13DoubleCountedBudgetSurface_doubleCountedAtom

theorem exact_budget_surface_side_conditions_equivalent_regression :
    v13ExactAtomicBudgetSurface.NoDoubleCounting ↔
      v13ExactAtomicBudgetSurface.AllPositiveCostAtomsCharged := by
  exact
    V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
      v13ExactAtomicBudgetSurface
      v13ExactAtomicBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem cancellation_budget_surface_side_conditions_equivalent_regression :
    v13CancellationBudgetSurface.NoDoubleCounting ↔
      v13CancellationBudgetSurface.AllPositiveCostAtomsCharged := by
  exact
    V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
      v13CancellationBudgetSurface
      v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget

theorem cancellation_budget_surface_exact_budget_but_both_side_conditions_false_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      ¬ v13CancellationBudgetSurface.NoDoubleCounting ∧
      ¬ v13CancellationBudgetSurface.AllPositiveCostAtomsCharged := by
  exact
    ⟨v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget,
      v13CancellationBudgetSurface_not_noDoubleCounting,
      v13CancellationBudgetSurface_not_allPositiveCostAtomsCharged⟩

end Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetEqualitySharpnessRegression
