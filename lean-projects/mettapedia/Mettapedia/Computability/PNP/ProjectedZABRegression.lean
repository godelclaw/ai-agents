import Mettapedia.Computability.PNP.ProjectedZABCompressionObstruction
import Mathlib.Tactic

/-!
# Projected `(z, a, b)` Route Regression

Small theorem-level checks for projected exact `z+a+b` routes.

These fixtures consume the projected `BitVec` obstruction endpoints directly on
small parameter choices, so both the named ERM family and the final projected
recovery wrapper stay pinned to the intended truth-table contradictions.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.ProjectedZABRegression

open scoped ENNReal

section

section FiniteImageObjects

variable {n r k : ℕ} {Index : Type*}

theorem projected_zab_family_finite_predictor_cover_regression
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact projectedZABDecisionListERMFinitePredictorCover
    (n := n) (r := r) (k := k) (Index := Index) coords samples

theorem projected_zab_family_finite_representative_cover_regression
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FiniteIndexRepresentativeCover
      (2 ^ (r + 2 * k + 1)) := by
  exact projectedZABDecisionListERMFiniteIndexRepresentativeCover
    (n := n) (r := r) (k := k) (Index := Index) coords samples

theorem projected_zab_family_finite_predictor_quotient_regression
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FinitePredictorQuotient
      (2 ^ (r + 2 * k + 1)) := by
  exact projectedZABDecisionListERMFinitePredictorQuotient
    (n := n) (r := r) (k := k) (Index := Index) coords samples

theorem projected_zab_recovery_finite_predictor_cover_regression
    [Fintype (BitVec n)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem projected_zab_recovery_finite_representative_cover_regression
    [Fintype (BitVec n)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finiteIndexRepresentativeCover

theorem projected_zab_recovery_finite_predictor_quotient_regression
    [Fintype (BitVec n)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorQuotient

end FiniteImageObjects

variable {Index : Type*}

theorem projected_zab_family_small_width_regression
    (coords : Fin 1 → Fin 2)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := 2) (r := 1) (k := 1) (Index := Index) coords samples).predict := by
  exact
    projectedZABDecisionListERMFamily_not_surjective_of_le_of_two_le
      (n := 2) (r := 1) (k := 1) (Index := Index)
      coords samples (by norm_num) (by norm_num)

theorem projected_zab_recovery_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {coords : Fin 1 → Fin 2}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ProjectedZABERMRecoveryData
        (n := 2) (r := 1) (k := 1) (Index := Index) μ coords G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

end

end Mettapedia.Computability.PNP.ProjectedZABRegression
