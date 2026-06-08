import Mettapedia.Computability.PNP.PNPv13CruxLedger
import Mathlib.Tactic

/-!
# PNP v13 atomic evidence budget boundary

The v13 ledger asks for safe-buffer leakage and hidden-gauge rank to bound a
coordinate-summed advantage.  This file isolates the finite bookkeeping theorem
that any such bound must satisfy: if the same positive-cost evidence atom is
charged by more than one coordinate, the coordinate-summed budget must pay that
multiplicity.  A one-atom/two-coordinate model gives the minimal obstruction to
using the atom budget without a no-double-counting theorem.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- Abstract finite budget surface for the v13 atomic-evidence step.  A
coordinate may charge an evidence atom; each atom has a nonnegative cost. -/
structure V13AtomicEvidenceBudgetSurface (Coord : Type u) (Atom : Type v) where
  charges : Coord → Atom → Prop
  atomCost : Atom → Nat

namespace V13AtomicEvidenceBudgetSurface

/-- How many coordinates charge an atom. -/
def atomMultiplicity {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] (a : Atom) : Nat :=
  ∑ c : Coord, if S.charges c a then 1 else 0

/-- The raw atom budget, with every atom paid once. -/
def atomBudget {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Atom] : Nat :=
  ∑ a : Atom, S.atomCost a

/-- The coordinate-summed cost, grouped by atoms.  The multiplicity factor is
the bookkeeping point: charging the same atom from two coordinates costs twice. -/
def coordinateSummedCost {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges] : Nat :=
  ∑ a : Atom, S.atomMultiplicity a * S.atomCost a

/-- No positive-cost atom is charged by more than one coordinate. -/
def NoDoubleCounting {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] : Prop :=
  ∀ a, 0 < S.atomCost a → S.atomMultiplicity a ≤ 1

/-- A concrete double-counting witness: a positive-cost atom charged by at
least two coordinates. -/
def DoubleCountedAtom {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] : Prop :=
  ∃ a, 0 < S.atomCost a ∧ 1 < S.atomMultiplicity a

/-- No-double-counting is exactly the absence of a positive-cost atom with
multiplicity at least two. -/
theorem noDoubleCounting_iff_not_doubleCountedAtom
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [DecidableRel S.charges] :
    S.NoDoubleCounting ↔ ¬ S.DoubleCountedAtom := by
  constructor
  · intro hno hdouble
    rcases hdouble with ⟨a, hcost, hmult⟩
    exact (not_lt_of_ge (hno a hcost)) hmult
  · intro hnot a hcost
    by_contra hle
    have hmult : 1 < S.atomMultiplicity a := by omega
    exact hnot ⟨a, hcost, hmult⟩

/-- If positive-cost atoms are never charged twice, the coordinate-summed cost
is bounded by the once-per-atom budget. -/
theorem coordinateSummedCost_le_atomBudget_of_noDoubleCounting
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hno : S.NoDoubleCounting) :
    S.coordinateSummedCost ≤ S.atomBudget := by
  classical
  dsimp [coordinateSummedCost, atomBudget]
  refine Finset.sum_le_sum ?_
  intro a _ha
  by_cases hcost : 0 < S.atomCost a
  · have hmul :
        S.atomMultiplicity a * S.atomCost a ≤ 1 * S.atomCost a :=
      Nat.mul_le_mul_right (S.atomCost a) (hno a hcost)
    simpa using hmul
  · have hzero : S.atomCost a = 0 := by omega
    simp [hzero]

/-- Any strict failure of the once-per-atom budget exposes a double-counted
positive-cost atom. -/
theorem doubleCountedAtom_of_atomBudget_lt_coordinateSummedCost
    {Coord : Type u} {Atom : Type v}
    (S : V13AtomicEvidenceBudgetSurface Coord Atom) [Fintype Coord]
    [Fintype Atom] [DecidableRel S.charges]
    (hlt : S.atomBudget < S.coordinateSummedCost) :
    S.DoubleCountedAtom := by
  classical
  by_contra hdouble
  have hno : S.NoDoubleCounting :=
    (S.noDoubleCounting_iff_not_doubleCountedAtom).2 hdouble
  have hle : S.coordinateSummedCost ≤ S.atomBudget :=
    S.coordinateSummedCost_le_atomBudget_of_noDoubleCounting hno
  omega

end V13AtomicEvidenceBudgetSurface

/-- The smallest budget countermodel: two coordinates both charge one shared
positive-cost evidence atom. -/
def v13DoubleCountedBudgetSurface :
    V13AtomicEvidenceBudgetSurface (Fin 2) (Fin 1) where
  charges := fun _ _ => True
  atomCost := fun _ => 1

instance v13DoubleCountedBudgetSurface_decidableRel :
    DecidableRel v13DoubleCountedBudgetSurface.charges :=
  fun _ _ => isTrue trivial

/-- The shared atom is charged by both coordinates. -/
theorem v13DoubleCountedBudgetSurface_atomMultiplicity_zero :
    v13DoubleCountedBudgetSurface.atomMultiplicity 0 = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13DoubleCountedBudgetSurface]

/-- The once-per-atom budget pays the shared atom once. -/
theorem v13DoubleCountedBudgetSurface_atomBudget :
    v13DoubleCountedBudgetSurface.atomBudget = 1 := by
  norm_num [V13AtomicEvidenceBudgetSurface.atomBudget,
    v13DoubleCountedBudgetSurface]

/-- The coordinate-summed cost pays the shared atom twice. -/
theorem v13DoubleCountedBudgetSurface_coordinateSummedCost :
    v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 := by
  norm_num [V13AtomicEvidenceBudgetSurface.coordinateSummedCost,
    V13AtomicEvidenceBudgetSurface.atomMultiplicity,
    v13DoubleCountedBudgetSurface]

/-- The toy surface has a positive-cost double-counted atom. -/
theorem v13DoubleCountedBudgetSurface_doubleCountedAtom :
    v13DoubleCountedBudgetSurface.DoubleCountedAtom := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [v13DoubleCountedBudgetSurface]
  · simp [v13DoubleCountedBudgetSurface_atomMultiplicity_zero]

/-- Therefore the toy surface does not satisfy the no-double-counting premise. -/
theorem v13DoubleCountedBudgetSurface_not_noDoubleCounting :
    ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting := by
  intro hno
  have hle : v13DoubleCountedBudgetSurface.atomMultiplicity 0 ≤ 1 :=
    hno 0 (by norm_num [v13DoubleCountedBudgetSurface])
  rw [v13DoubleCountedBudgetSurface_atomMultiplicity_zero] at hle
  omega

/-- In the toy surface, the coordinate-summed cost strictly exceeds the atom
budget. -/
theorem v13DoubleCountedBudgetSurface_atomBudget_lt_coordinateSummedCost :
    v13DoubleCountedBudgetSurface.atomBudget <
      v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  rw [v13DoubleCountedBudgetSurface_atomBudget,
    v13DoubleCountedBudgetSurface_coordinateSummedCost]
  norm_num

end Mettapedia.Computability.PNP
