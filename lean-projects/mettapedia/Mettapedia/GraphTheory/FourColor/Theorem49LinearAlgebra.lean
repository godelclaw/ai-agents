import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mettapedia.GraphTheory.FourColor.Orthogonality

namespace Mettapedia.GraphTheory.FourColor

open LinearMap Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Finite-dimensional orthogonal-separation bridge for the algebraic side of Theorem 4.9.
If a candidate generator space `W` lies in the target space `T`, and no nonzero vector of `T`
annihilates `W` under a nondegenerate reflexive bilinear form, then `W` is already all of `T`.

This is the linear-algebra content behind the move from the proved annihilator endpoint to the
paper's spanning conclusion. -/
theorem submodule_eq_of_le_of_inf_orthogonal_eq_bot [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hB : B.Nondegenerate) (hB₀ : B.IsRefl)
    {W T : Submodule K E} (hWT : W ≤ T)
    (hdisj : T ⊓ B.orthogonal W = ⊥) :
    W = T := by
  refine Submodule.eq_of_le_of_finrank_le hWT ?_
  have hdisjoint : Disjoint T (B.orthogonal W) := by
    rw [disjoint_iff_inf_le]
    exact hdisj.le
  have hsum :
      finrank K T + finrank K (B.orthogonal W) ≤ finrank K E :=
    Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  have horth :
      finrank K (B.orthogonal W) = finrank K E - finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hB hB₀ W
  have hWle : finrank K W ≤ finrank K E := Submodule.finrank_le W
  omega

section ChainDot

open scoped BigOperators

variable (E : Type*) [Fintype E]

/-- The standard finite chain dot product as an `𝔽₂`-bilinear form on color-valued chains. -/
noncomputable def chainDotBilinForm : LinearMap.BilinForm F2 (E → Color) := by
  classical
  refine LinearMap.mk₂ F2 (fun x y => ∑ e, colorDot (x e) (y e)) ?_ ?_ ?_ ?_
  · intro x x' y
    simp [colorDot, Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm]
  · intro a x y
    simp [colorDot, Finset.mul_sum, mul_add, mul_comm, mul_left_comm]
  · intro x y y'
    simp [colorDot, Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm]
  · intro a x y
    simp [colorDot, Finset.mul_sum, mul_add, mul_left_comm]

@[simp] theorem chainDotBilinForm_apply (x y : E → Color) :
    chainDotBilinForm E x y = ∑ e, colorDot (x e) (y e) :=
  rfl

theorem chainDotBilinForm_single_right [DecidableEq E] (x : E → Color) (e : E) (c : Color) :
    chainDotBilinForm E x (Pi.single e c) = colorDot (x e) c := by
  classical
  rw [chainDotBilinForm_apply, Finset.sum_eq_single e]
  · simp
  · intro e' _ he'
    simp [Pi.single_eq_of_ne he']
  · intro he
    simp at he

theorem chainDotBilinForm_single_left [DecidableEq E] (x : E → Color) (e : E) (c : Color) :
    chainDotBilinForm E (Pi.single e c) x = colorDot c (x e) := by
  classical
  rw [chainDotBilinForm_apply, Finset.sum_eq_single e]
  · simp
  · intro e' _ he'
    simp [Pi.single_eq_of_ne he']
  · intro he
    simp at he

theorem color_eq_zero_of_colorDot_red_blue {c : Color}
    (hr : colorDot c red = 0) (hb : colorDot c blue = 0) :
    c = 0 := by
  rcases c with ⟨r, b⟩
  simp [colorDot, red, blue] at hr hb ⊢
  exact ⟨hr, hb⟩

theorem chainDotBilinForm_isSymm : (chainDotBilinForm E).IsSymm := by
  constructor
  intro x y
  simp [chainDotBilinForm, colorDot, mul_comm]

theorem chainDotBilinForm_isRefl : (chainDotBilinForm E).IsRefl :=
  (chainDotBilinForm_isSymm E).isRefl

theorem chainDotBilinForm_nondegenerate : (chainDotBilinForm E).Nondegenerate := by
  classical
  constructor
  · intro x hx
    funext e
    apply color_eq_zero_of_colorDot_red_blue
    · have h := hx (Pi.single e red)
      rwa [chainDotBilinForm_single_right] at h
    · have h := hx (Pi.single e blue)
      rwa [chainDotBilinForm_single_right] at h
  · intro y hy
    funext e
    apply color_eq_zero_of_colorDot_red_blue
    · have h := hy (Pi.single e red)
      rw [chainDotBilinForm_single_left] at h
      simpa [colorDot, red] using h
    · have h := hy (Pi.single e blue)
      rw [chainDotBilinForm_single_left] at h
      simpa [colorDot, blue] using h

end ChainDot

end Mettapedia.GraphTheory.FourColor
