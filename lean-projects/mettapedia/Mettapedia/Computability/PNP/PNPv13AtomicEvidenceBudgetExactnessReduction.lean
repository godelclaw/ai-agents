import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetEqualitySharpness
import Mathlib.Tactic

/-!
# PNP v13 atomic evidence budget exactness reduction

The equality-sharpness file proves that on the exact-budget surface,
`NoDoubleCounting` and `AllPositiveCostAtomsCharged` are equivalent.  This file
packages the actual route obligation and blocks the next misuse: equivalence of
the two side conditions is still weaker than either one being true.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace V13AtomicEvidenceBudgetSurface

/-- The full structural exactness obligation for the v13 atomic-budget step:
no positive-cost atom is double-counted and no positive-cost atom is omitted. -/
def ExactnessSideConditions {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] : Prop :=
  S.NoDoubleCounting ∧ S.AllPositiveCostAtomsCharged

/-- The full exactness-side conjunction is sufficient for exact budget reuse. -/
theorem coordinateSummedCost_eq_atomBudget_of_exactnessSideConditions
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hexact : S.ExactnessSideConditions) :
    S.coordinateSummedCost = S.atomBudget := by
  exact
    S.coordinateSummedCost_eq_atomBudget_of_noDoubleCounting_of_allPositiveCostAtomsCharged
      hexact.1 hexact.2

/-- On the equality surface, the full exactness conjunction reduces to the
no-double-counting side condition alone. -/
theorem exactnessSideConditions_iff_noDoubleCounting_of_coordinateSummedCost_eq_atomBudget
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.ExactnessSideConditions ↔ S.NoDoubleCounting := by
  constructor
  · intro hexact
    exact hexact.1
  · intro hno
    exact
      ⟨hno,
        S.allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget_of_noDoubleCounting
          heq hno⟩

/-- On the equality surface, the full exactness conjunction also reduces to the
positive-cost coverage side condition alone. -/
theorem exactnessSideConditions_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (heq : S.coordinateSummedCost = S.atomBudget) :
    S.ExactnessSideConditions ↔ S.AllPositiveCostAtomsCharged := by
  constructor
  · intro hexact
    exact hexact.2
  · intro hall
    exact
      ⟨S.noDoubleCounting_of_coordinateSummedCost_eq_atomBudget_of_allPositiveCostAtomsCharged
          heq hall,
        hall⟩

end V13AtomicEvidenceBudgetSurface

/-- Concrete route anchor: exact aggregate budget equality together with the
equality-surface equivalence of the two structural side conditions still does
not force the actual exactness conjunction. -/
theorem v13CancellationBudgetSurface_exact_budget_with_sideConditionEquivalence_without_exactnessSideConditions :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  refine ⟨v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget, ?_, ?_⟩
  · exact
      V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
        v13CancellationBudgetSurface
        v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget
  · intro hexact
    exact v13CancellationBudgetSurface_not_noDoubleCounting hexact.1

/-- Exact budget equality plus equivalence of the two structural side
conditions still does not imply the exactness conjunction itself. -/
theorem not_forall_coordinateSummedCost_eq_atomBudget_and_sideConditionEquivalence_implies_exactnessSideConditions :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
          S.ExactnessSideConditions := by
  intro hall
  have hexact : v13CancellationBudgetSurface.ExactnessSideConditions :=
    hall (S := v13CancellationBudgetSurface)
      v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget
      (V13AtomicEvidenceBudgetSurface.noDoubleCounting_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
        v13CancellationBudgetSurface
        v13CancellationBudgetSurface_coordinateSummedCost_eq_atomBudget)
  exact v13CancellationBudgetSurface_not_noDoubleCounting hexact.1

end Mettapedia.Computability.PNP
