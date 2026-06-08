import Mettapedia.Computability.PNP.SharedExactABCompressionObstruction
import Mathlib.Tactic

/-!
# Shared Exact `(a, b)` Route Regression

Small theorem-level checks for the shared-basis raw exact `(a, b)` route.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.SharedExactABRegression

open scoped ENNReal

section

variable {Index : Type*}

theorem shared_exact_ab_decision_list_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {features : Fin 1 → AffineColumnCode (1 + 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ features G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem shared_exact_ab_affine_feature_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_lt_visibleWidth (by norm_num)

theorem shared_exact_ab_sparse_threshold_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem shared_exact_ab_raw_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem shared_exact_ab_route_small_width_regression
    (features : Fin 1 → AffineColumnCode (1 + 1))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := BitVec 2) (r := 1) (k := 1) features samples).predict := by
  exact
    sharedExactABAffineDecisionListERMFamily_not_surjective_of_le_of_two_le
      (n := 2) (r := 1) (k := 1) (Index := Index) features samples
      (by norm_num) (by norm_num)

end

end Mettapedia.Computability.PNP.SharedExactABRegression
