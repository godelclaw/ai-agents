import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzData
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Schwartz Directional Rigidity on `ℝ^3`

This file records a basic obstruction for finite-energy Schwartz profiles on the
concrete Navier--Stokes space `ℝ^3`.

Any Schwartz profile that is invariant under translation along a nonzero
direction must vanish identically.  Equivalently, if the directional Fréchet
derivative along a fixed nonzero direction vanishes everywhere, then the
profile must be zero.

This isolates a structural reason why line-invariant shear-style ansatzes from
the non-decaying lane do not transfer directly to the Schwartz lane.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped SchwartzMap

/-- Translation invariance of a profile along a fixed spatial direction. -/
def TranslationInvariantAlong {F : Type*} (v : NSSpace) (f : NSSpace → F) : Prop :=
  ∀ x : NSSpace, ∀ s : ℝ, f (x + s • v) = f x

/-- If the directional Fréchet derivative of a profile vanishes everywhere
along a fixed direction `v`, then the profile is translation invariant along
the corresponding affine lines. -/
theorem translationInvariantAlong_of_fderiv_eq_zero_along
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : Differentiable ℝ f) {v : NSSpace}
    (hzero : ∀ x : NSSpace, fderiv ℝ f x v = 0) :
    TranslationInvariantAlong v f := by
  intro x s
  let line : ℝ → NSSpace := AffineMap.lineMap x (x + v)
  let g : ℝ → F := fun r => f (line r)
  have hgdiff : Differentiable ℝ g := by
    simpa [g, line] using hf.comp (AffineMap.lineMap x (x + v)).differentiable
  have hgzero : ∀ r : ℝ, deriv g r = 0 := by
    intro r
    have hline : HasDerivAt line v r := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := x + v) (x := r))
    have hcomp :
        HasDerivAt g ((fderiv ℝ f (line r)) v) r :=
      (hf (line r)).hasFDerivAt.comp_hasDerivAt r hline
    rw [hcomp.deriv, hzero (line r)]
  have hconst := is_const_of_deriv_eq_zero hgdiff hgzero s 0
  simpa [g, line, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc] using
    hconst

/-- A Schwartz profile on `ℝ^3` cannot be invariant along any nonzero
translation direction.  Decay forces every constant line-value to vanish. -/
theorem schwartzMap_eq_zero_of_translationInvariantAlong
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(NSSpace, F)) {v : NSSpace} (hv : v ≠ 0)
    (hinv : TranslationInvariantAlong v (f : NSSpace → F)) :
    f = 0 := by
  ext x
  by_contra hfx
  have hfxnorm : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
  let M : ℝ := (SchwartzMap.seminorm ℝ 1 0) f
  have hMnonneg : 0 ≤ M :=
    apply_nonneg (SchwartzMap.seminorm ℝ 1 0) f
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := (‖x‖ + M / ‖f x‖ + 1) / ‖v‖
  have hnum_nonneg : 0 ≤ ‖x‖ + M / ‖f x‖ + 1 := by
    have hdivnonneg : 0 ≤ M / ‖f x‖ := by
      positivity
    linarith [norm_nonneg x]
  have hrnonneg : 0 ≤ r := by
    exact div_nonneg hnum_nonneg (norm_nonneg v)
  have hrmul : r * ‖v‖ = ‖x‖ + M / ‖f x‖ + 1 := by
    have hvne : ‖v‖ ≠ 0 := ne_of_gt hvnorm
    simpa [r] using (div_mul_cancel₀ (‖x‖ + M / ‖f x‖ + 1) hvne)
  let y : NSSpace := x + r • v
  have hline_norm : ‖r • v‖ = ‖x‖ + M / ‖f x‖ + 1 := by
    calc
      ‖r • v‖ = |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = r * ‖v‖ := by simp [abs_of_nonneg hrnonneg]
      _ = ‖x‖ + M / ‖f x‖ + 1 := hrmul
  have hnorm_lower : M / ‖f x‖ + 1 ≤ ‖y‖ := by
    have htri : ‖r • v‖ ≤ ‖y‖ + ‖x‖ := by
      simpa [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_sub_le (x + r • v) x)
    linarith [hline_norm]
  have hbound : ‖y‖ * ‖f x‖ ≤ M := by
    have hseminorm := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 1 y
    have hyval : f y = f x := by
      simpa [y] using hinv x r
    simpa [M, y, hyval] using hseminorm
  have hmul_lower : M + ‖f x‖ ≤ ‖y‖ * ‖f x‖ := by
    have hmul :=
      mul_le_mul_of_nonneg_right hnorm_lower hfxnorm.le
    have hrewrite : (M / ‖f x‖ + 1) * ‖f x‖ = M + ‖f x‖ := by
      field_simp [hfxnorm.ne']
    rwa [hrewrite] at hmul
  have hstrict : M < ‖y‖ * ‖f x‖ := by
    have : M < M + ‖f x‖ := by
      linarith
    exact lt_of_lt_of_le this hmul_lower
  exact not_lt_of_ge hbound hstrict

/-- A Schwartz profile whose directional Fréchet derivative vanishes
everywhere along a fixed nonzero direction must vanish identically. -/
theorem schwartzMap_eq_zero_of_fderiv_eq_zero_along
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(NSSpace, F)) {v : NSSpace} (hv : v ≠ 0)
    (hzero : ∀ x : NSSpace, fderiv ℝ (fun z : NSSpace => f z) x v = 0) :
    f = 0 := by
  have hdiff : Differentiable ℝ (fun z : NSSpace => f z) := by
    simpa using f.smooth'.differentiable (by simp)
  exact
    schwartzMap_eq_zero_of_translationInvariantAlong f hv
      (translationInvariantAlong_of_fderiv_eq_zero_along (f := fun z : NSSpace => f z)
        hdiff hzero)

/-- Concrete initial-velocity specialization of
`schwartzMap_eq_zero_of_translationInvariantAlong`. -/
theorem schwartzInitialVelocity_eq_zero_of_translationInvariantAlong
    (u₀ : NSSchwartzInitialVelocity) {v : NSSpace} (hv : v ≠ 0)
    (hinv : TranslationInvariantAlong v (u₀ : NSInitialVelocity)) :
    (u₀ : NSInitialVelocity) = 0 := by
  simpa using
    congrArg (fun w : NSSchwartzInitialVelocity => (w : NSInitialVelocity))
      (schwartzMap_eq_zero_of_translationInvariantAlong u₀ hv hinv)

/-- Concrete initial-velocity specialization of
`schwartzMap_eq_zero_of_fderiv_eq_zero_along`. -/
theorem schwartzInitialVelocity_eq_zero_of_fderiv_eq_zero_along
    (u₀ : NSSchwartzInitialVelocity) {v : NSSpace} (hv : v ≠ 0)
    (hzero : ∀ x : NSSpace, fderiv ℝ (fun z : NSSpace => u₀ z) x v = 0) :
    (u₀ : NSInitialVelocity) = 0 := by
  simpa using
    congrArg (fun w : NSSchwartzInitialVelocity => (w : NSInitialVelocity))
      (schwartzMap_eq_zero_of_fderiv_eq_zero_along u₀ hv hzero)

end NavierStokes
end FluidDynamics
end Mettapedia
