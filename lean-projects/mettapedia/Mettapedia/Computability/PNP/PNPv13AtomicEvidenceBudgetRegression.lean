import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudget

/-!
# Regression checks for the PNP v13 atomic evidence budget boundary
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetRegression

open Mettapedia.Computability.PNP

universe u v

theorem no_double_counting_iff_not_double_counted_atom_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] :
    S.NoDoubleCounting ↔ ¬ S.DoubleCountedAtom := by
  exact V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_not_doubleCountedAtom S

theorem coordinate_summed_cost_le_atom_budget_of_no_double_counting_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) :
    S.coordinateSummedCost ≤ S.atomBudget := by
  exact
    V13AtomicEvidenceBudgetSurface.coordinateSummedCost_le_atomBudget_of_noDoubleCounting
      S hno

theorem double_counted_atom_of_atom_budget_lt_coordinate_summed_cost_regression
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hlt : S.atomBudget < S.coordinateSummedCost) :
    S.DoubleCountedAtom := by
  exact
    V13AtomicEvidenceBudgetSurface.doubleCountedAtom_of_atomBudget_lt_coordinateSummedCost
      S hlt

theorem double_counted_budget_surface_atom_budget_regression :
    v13DoubleCountedBudgetSurface.atomBudget = 1 := by
  exact v13DoubleCountedBudgetSurface_atomBudget

theorem double_counted_budget_surface_coordinate_summed_cost_regression :
    v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 := by
  exact v13DoubleCountedBudgetSurface_coordinateSummedCost

theorem double_counted_budget_surface_blocks_no_double_counting_regression :
    ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting := by
  exact v13DoubleCountedBudgetSurface_not_noDoubleCounting

theorem double_counted_budget_surface_exceeds_atom_budget_regression :
    v13DoubleCountedBudgetSurface.atomBudget <
      v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact v13DoubleCountedBudgetSurface_atomBudget_lt_coordinateSummedCost

end Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetRegression
