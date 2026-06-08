import Mettapedia.Computability.PNP.WeightAsymmetryObstruction

/-!
# Regression checks for weight-asymmetry obstruction

These wrappers pin the pointwise repair burden for invariant soft scores:
nonzero signed signal requires a nonzero-score point whose sample weight changes
across the involution.
-/

namespace Mettapedia.Computability.PNP.WeightAsymmetryObstructionRegression

open Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

theorem score_support_weight_symmetric_zero_signal_regression
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 := by
  exact
    signedScore_sum_eq_zero_of_score_support_weight_symmetric
      τ u y w score hτ hu hy hsym

theorem nonzero_signal_exposes_weight_asymmetric_score_point_regression
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 := by
  exact
    exists_weight_asymmetric_score_point_of_signedScore_sum_ne_zero
      τ u y w score hτ hu hy hsignal

end

end Mettapedia.Computability.PNP.WeightAsymmetryObstructionRegression
