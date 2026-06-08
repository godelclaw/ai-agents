import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

variable {ι E : Type*} [DecidableEq ι]

/-- Finite sums of color-valued chains preserve vanishing on any common boundary set. -/
theorem sum_zero_on_boundary
    {S : Finset ι} {f : ι → E → Color} {boundary : Finset E}
    (hzero : ∀ i ∈ S, ∀ e ∈ boundary, f i e = 0) :
    ∀ e ∈ boundary, (Finset.sum S f) e = 0 := by
  classical
  intro e he
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert i S hi ih =>
      have hzeroS : ∀ j ∈ S, ∀ e ∈ boundary, f j e = 0 := by
        intro j hj e' he'
        exact hzero j (by simp [hj]) e' he'
      have hzeroI : f i e = 0 := hzero i (by simp) e he
      have hrest : (Finset.sum S f) e = 0 := ih hzeroS
      calc
        (Finset.sum (insert i S) f) e = (f i + Finset.sum S f) e := by
          simp [Finset.sum_insert, hi]
        _ = f i e + (Finset.sum S f) e := by
          simp
        _ = 0 + 0 := by
          rw [hzeroI, hrest]
        _ = 0 := by
          simp

end Mettapedia.GraphTheory.FourColor
