import Mettapedia.Computability.PNP.SharedExactZABCompressionObstruction
import Mathlib.Tactic

/-!
# Shared Exact `(zfeat(z), a, b)` Route Regression

Small theorem-level checks for the shared-basis exact `z+a+b` route.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.SharedExactZABRegression

open scoped ENNReal

section

variable {Index : Type*}

theorem shared_exact_zab_decision_list_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {features : Fin 1 → AffineColumnCode (1 + (1 + 1))}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index)
        μ zfeat features G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem shared_exact_zab_affine_feature_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_lt_visibleWidth (by norm_num)

theorem shared_exact_zab_affine_feature_erm_finite_image_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (2 ^ 1)) ∧
      G.FiniteIndexRepresentativeCover (2 ^ (2 ^ 1)) ∧
      G.FinitePredictorQuotient (2 ^ (2 ^ 1)) := by
  exact ⟨h.finitePredictorCover, h.finiteIndexRepresentativeCover, h.finitePredictorQuotient⟩

theorem shared_exact_zab_sparse_threshold_erm_small_budget_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_budget_lt (by norm_num)

theorem shared_exact_zab_sparse_threshold_erm_finite_image_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (2 * 1)) ∧
      G.FiniteIndexRepresentativeCover (2 ^ (2 * 1)) ∧
      G.FinitePredictorQuotient (2 ^ (2 * 1)) := by
  exact ⟨h.finitePredictorCover, h.finiteIndexRepresentativeCover, h.finitePredictorQuotient⟩

theorem shared_exact_zab_raw_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem shared_exact_zab_raw_erm_finite_image_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec 2) (p := 1) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (1 + 1)) ∧
      G.FiniteIndexRepresentativeCover (2 ^ (1 + 1)) ∧
      G.FinitePredictorQuotient (2 ^ (1 + 1)) := by
  exact ⟨h.finitePredictorCover, h.finiteIndexRepresentativeCover, h.finitePredictorQuotient⟩

theorem shared_exact_zab_route_small_width_regression
    (zfeat : BitVec 2 → BitVec 1)
    (features : Fin 1 → AffineColumnCode (1 + (1 + 1)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec 2) (p := 1) (r := 1) (k := 1)
          zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_le_of_two_le
      (n := 2) (p := 1) (r := 1) (k := 1) (Index := Index)
      zfeat features samples (by norm_num) (by norm_num)

end

end Mettapedia.Computability.PNP.SharedExactZABRegression
