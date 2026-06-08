import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

/-- The coordinatewise `𝔽₂` dot product on `𝔽₂²`. -/
def colorDot (x y : Color) : F2 :=
  x.1 * y.1 + x.2 * y.2

@[simp] theorem colorDot_zero_left (x : Color) : colorDot 0 x = 0 := by
  simp [colorDot]

@[simp] theorem colorDot_zero_right (x : Color) : colorDot x 0 = 0 := by
  simp [colorDot]

@[simp] theorem colorDot_red_right (x : Color) : colorDot x red = x.1 := by
  simp [colorDot, red]

@[simp] theorem colorDot_blue_right (x : Color) : colorDot x blue = x.2 := by
  simp [colorDot, blue]

@[simp] theorem colorDot_purple_right (x : Color) : colorDot x purple = x.1 + x.2 := by
  simp [colorDot, purple]

theorem eq_zero_or_eq_red_or_eq_blue_or_eq_purple (c : Color) :
    c = 0 ∨ c = red ∨ c = blue ∨ c = purple := by
  rcases c with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> simp [red, blue, purple]

theorem eq_red_or_eq_blue_or_eq_purple_of_ne_zero (c : Color) (hc : c ≠ 0) :
    c = red ∨ c = blue ∨ c = purple := by
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple c with h0 | hr | hb | hp
  · exact False.elim (hc h0)
  · exact Or.inl hr
  · exact Or.inr <| Or.inl hb
  · exact Or.inr <| Or.inr hp

/-- A color that annihilates both nonzero colors different from `d` must vanish. This is the local
`𝔽₂²` algebra used in the leaf-elimination step of Theorem 4.9. -/
theorem eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne {z d : Color} (hd : d ≠ 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d → colorDot z γ = 0) :
    z = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl
  · rcases z with ⟨x, y⟩
    have hy : y = 0 := by
      simpa [colorDot, blue] using horth blue blue_ne_zero (by decide)
    have hxy : x + y = 0 := by
      simpa [colorDot, purple] using horth purple purple_ne_zero (by decide)
    have hx : x = 0 := by simpa [hy] using hxy
    simp [hx, hy]
  · rcases z with ⟨x, y⟩
    have hx : x = 0 := by
      simpa [colorDot, red] using horth red red_ne_zero (by decide)
    have hxy : x + y = 0 := by
      simpa [colorDot, purple] using horth purple purple_ne_zero (by decide)
    have hy : y = 0 := by simpa [hx] using hxy
    simp [hx, hy]
  · rcases z with ⟨x, y⟩
    have hx : x = 0 := by
      simpa [colorDot, red] using horth red red_ne_zero (by decide)
    have hy : y = 0 := by
      simpa [colorDot, blue] using horth blue blue_ne_zero (by decide)
    simp [hx, hy]

/-- Dot product of two color chains restricted to a finite edge set. -/
def chainDot {E : Type*} [DecidableEq E] (S : Finset E) (x y : E → Color) : F2 :=
  Finset.sum S fun e => colorDot (x e) (y e)

/-- If a chain vanishes on every edge of `S` except `e`, the chain-dot with an indicator chain on
`S` reduces to the single contribution at `e`. -/
theorem chainDot_indicatorChain_eq_colorDot_of_erase_zero {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {x : E → Color} {e : E}
    (he : e ∈ S) (hzero : ∀ e' ∈ S.erase e, x e' = 0) :
    chainDot S x (indicatorChain γ S) = colorDot (x e) γ := by
  unfold chainDot
  have hsplit :
      Finset.sum S (fun e' => colorDot (x e') (indicatorChain γ S e')) =
        Finset.sum (S.erase e) (fun e' => colorDot (x e') (indicatorChain γ S e')) +
          colorDot (x e) (indicatorChain γ S e) := by
    simpa using
      (Finset.sum_erase_add
        (s := S)
        (a := e)
        (f := fun e' => colorDot (x e') (indicatorChain γ S e'))
        he).symm
  rw [hsplit]
  have hrest : Finset.sum (S.erase e) (fun e' => colorDot (x e') (indicatorChain γ S e')) = 0 := by
    apply Finset.sum_eq_zero
    intro e' he'
    have hx0 : x e' = 0 := hzero e' he'
    have hmemS : e' ∈ S := Finset.mem_of_mem_erase he'
    simp [hx0, indicatorChain_apply_of_mem γ hmemS]
  rw [hrest, zero_add, indicatorChain_apply_of_mem γ he]

/-- Local annihilator step for Theorem 4.9: if `z` is orthogonal to the indicator chains supported
on the two nonzero colors different from `d`, and those supports contain no other nonzero
contribution of `z`, then `z` vanishes on the distinguished edge `e`. -/
theorem edge_eq_zero_of_annihilates_other_nonzero_colors {E : Type*} [DecidableEq E]
    (support : Color → Finset E) (z : E → Color) {e : E} {d : Color}
    (hd : d ≠ 0)
    (hmem : ∀ γ, γ ≠ 0 → γ ≠ d → e ∈ support γ)
    (hzero : ∀ γ, γ ≠ 0 → γ ≠ d → ∀ e' ∈ (support γ).erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d →
      chainDot (support γ) z (indicatorChain γ (support γ)) = 0) :
    z e = 0 := by
  have hdot : ∀ γ, γ ≠ 0 → γ ≠ d → colorDot (z e) γ = 0 := by
    intro γ hγ0 hγd
    rw [← chainDot_indicatorChain_eq_colorDot_of_erase_zero γ
      (hmem γ hγ0 hγd) (hzero γ hγ0 hγd)]
    exact horth γ hγ0 hγd
  exact eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne hd hdot

end Mettapedia.GraphTheory.FourColor
