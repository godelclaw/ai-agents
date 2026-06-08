import Mettapedia.Computability.PNP.ExactABCompressionObstruction
import Mathlib.Tactic

/-!
# Exact `(a, b)` Route Regression

Small theorem-level checks for the exact non-shared raw `(a, b)` route.

These fixtures consume the concrete `BitVec` obstruction endpoints directly on
small parameter choices, so the manuscript-facing recovery wrappers remain
connected to the intended truth-table contradictions.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.ExactABRegression

open scoped ENNReal

section

variable {Index : Type*}

theorem exact_ab_route_small_budget_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (exactABAffineDecisionListERMFamily
          (Z := BitVec 2) (r := 1) (k := 1) samples).predict := by
  exact
    exactABAffineDecisionListERMFamily_not_surjective_of_budget_lt
      (n := 2) (r := 1) (k := 1) (Index := Index) samples
      (by norm_num)

theorem exact_ab_affine_feature_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_ab_sparse_threshold_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_ab_affine_decision_list_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_ab_raw_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

end

end Mettapedia.Computability.PNP.ExactABRegression
