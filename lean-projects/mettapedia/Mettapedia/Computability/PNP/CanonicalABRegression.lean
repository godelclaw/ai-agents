import Mettapedia.Computability.PNP.CanonicalABCompressionObstruction
import Mathlib.Tactic

/-!
# Canonical `(a, b)` Route Regression

Small theorem-level checks for the canonical raw `(a, b)` route.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PNP.CanonicalABRegression

open scoped ENNReal

section

variable {Index : Type*}

theorem canonical_ab_decision_list_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABDecisionListRecoveryData
        (Z := BitVec 2) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_two_le (by norm_num)

theorem canonical_ab_raw_erm_small_width_regression
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 1)}
    {G : ExactVisibleSwitchedFamily (BitVec 2) 1 Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := BitVec 2) (k := 1) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_two_le (by norm_num)

theorem canonical_ab_route_small_width_regression
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool) :
    ¬ Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := BitVec 2) (k := 1) samples).predict := by
  exact
    canonicalABDecisionListERMFamily_not_surjective_of_two_le
      (n := 2) (k := 1) (Index := Index) samples (by norm_num)

end

end Mettapedia.Computability.PNP.CanonicalABRegression
