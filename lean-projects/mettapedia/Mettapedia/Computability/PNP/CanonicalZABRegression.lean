import Mettapedia.Computability.PNP.CanonicalZABCompressionObstruction
import Mathlib.Tactic

/-!
# Canonical `(zfeat(z), a, b)` Route Regression

Small theorem-level checks for the canonical exact `z+a+b` route.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.CanonicalZABRegression

open scoped ENNReal

section

section FiniteImageObjects

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable {zfeat : Z → BitVec r}
variable {G : ExactVisibleSwitchedFamily Z k Index}

theorem canonical_zab_candidate_finite_predictor_cover_regression
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem canonical_zab_candidate_finite_representative_cover_regression
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finiteIndexRepresentativeCover

theorem canonical_zab_candidate_finite_predictor_quotient_regression
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorQuotient

theorem canonical_zab_code_family_finite_predictor_cover_regression
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes).FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact finitePredictorCover_canonicalZABCodeFamily
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes

theorem canonical_zab_code_family_finite_representative_cover_regression
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (canonicalZABCodeFamily
      (Z := Z) (r := r) (k := k) zfeat codes).FiniteIndexRepresentativeCover
      (2 ^ (r + 2 * k + 1)) := by
  exact finiteIndexRepresentativeCover_canonicalZABCodeFamily
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes

theorem canonical_zab_code_family_finite_predictor_quotient_regression
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (canonicalZABCodeFamily (Z := Z) (r := r) (k := k) zfeat codes).FinitePredictorQuotient
      (2 ^ (r + 2 * k + 1)) := by
  exact finitePredictorQuotient_canonicalZABCodeFamily
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes

theorem canonical_zab_recovery_finite_predictor_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem canonical_zab_recovery_finite_representative_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finiteIndexRepresentativeCover

theorem canonical_zab_recovery_finite_predictor_quotient_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorQuotient

theorem canonical_zab_erm_family_finite_predictor_cover_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact canonicalZABDecisionListERMFinitePredictorCover
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem canonical_zab_erm_family_finite_representative_cover_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FiniteIndexRepresentativeCover
      (2 ^ (r + 2 * k + 1)) := by
  exact canonicalZABDecisionListERMFiniteIndexRepresentativeCover
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem canonical_zab_erm_family_finite_predictor_quotient_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) zfeat samples).FinitePredictorQuotient
      (2 ^ (r + 2 * k + 1)) := by
  exact canonicalZABDecisionListERMFinitePredictorQuotient
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem canonical_zab_erm_recovery_finite_predictor_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem canonical_zab_erm_recovery_finite_representative_cover_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finiteIndexRepresentativeCover

theorem canonical_zab_erm_recovery_finite_predictor_quotient_regression
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorQuotient

end FiniteImageObjects

variable {Index : Type*}

theorem canonical_zab_decision_list_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem canonical_zab_raw_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {zfeat : BitVec 2 → BitVec 1}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := BitVec 2) (r := 1) (k := 1) (Index := Index) μ zfeat G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_le_of_two_le (by norm_num) (by norm_num)

theorem canonical_zab_route_small_width_regression
    (zfeat : BitVec 2 → BitVec 1)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec 2) (r := 1) (k := 1) zfeat samples).predict := by
  exact
    canonicalZABDecisionListERMFamily_not_surjective_of_le_of_two_le
      (n := 2) (r := 1) (k := 1) (Index := Index) zfeat samples
      (by norm_num) (by norm_num)

end

end Mettapedia.Computability.PNP.CanonicalZABRegression
