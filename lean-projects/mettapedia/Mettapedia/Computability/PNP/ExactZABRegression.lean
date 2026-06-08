import Mettapedia.Computability.PNP.ExactZABCompressionObstruction

/-!
# Exact `(zfeat(z), a, b)` Route Regression

Small theorem-level checks for the exact non-shared `z+a+b` route.

These fixtures consume the concrete `BitVec` obstruction endpoints directly on
small parameter choices, so the manuscript-facing recovery wrappers remain
connected to the intended truth-table contradictions.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.ExactZABRegression

open scoped ENNReal

section

section FiniteImageObjects

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable {zfeat : Z → BitVec r}
variable {G : ExactVisibleSwitchedFamily Z k Index}

theorem exact_zab_erm_family_finite_predictor_cover_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact exactZABDecisionListERMFinitePredictorCover
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem exact_zab_erm_family_finite_representative_cover_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FiniteIndexRepresentativeCover
      (2 ^ (r + 2 * k + 1)) := by
  exact exactZABDecisionListERMFiniteIndexRepresentativeCover
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem exact_zab_erm_family_finite_predictor_quotient_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FinitePredictorQuotient
      (2 ^ (r + 2 * k + 1)) := by
  exact exactZABDecisionListERMFinitePredictorQuotient
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem exact_zab_erm_recovery_finite_predictor_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem exact_zab_erm_recovery_finite_representative_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finiteIndexRepresentativeCover

theorem exact_zab_erm_recovery_finite_predictor_quotient_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorQuotient

end FiniteImageObjects

variable {Index : Type*}

theorem exact_zab_affine_feature_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index)
        μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_zab_sparse_threshold_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index)
        μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_zab_affine_decision_list_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index)
        μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem exact_zab_raw_decision_list_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index)
        μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem exact_zab_raw_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index)
        μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

end

end Mettapedia.Computability.PNP.ExactZABRegression
