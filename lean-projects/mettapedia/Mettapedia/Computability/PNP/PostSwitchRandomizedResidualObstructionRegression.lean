import Mettapedia.Computability.PNP.PostSwitchRandomizedResidualObstruction

/-!
# Regression checks for randomized residuals on the post-switch surface

These wrappers pin the manuscript-specialized randomized residual blocker:
exact local-input-invariant support leaves no positive joint resolving mass for
finite-coin randomized residuals on the post-switch surface.
-/

namespace Mettapedia.Computability.PNP.PostSwitchRandomizedResidualObstructionRegression

open Mettapedia.Computability.PNP

section

variable {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]

theorem invariant_support_zeroes_post_switch_randomized_resolved_mass_regression
    (v : PostSwitchInput Z k → Coin → V)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (hsupport : exactInputInvariantWeightedSupport w) :
    randomizedResidualResolvedMass tiInputMap v w coinWeight = 0 := by
  exact
    randomizedResidualResolvedMass_tiInputMap_eq_zero_of_exactInputInvariantWeightedSupport
      v w coinWeight hsupport

theorem positive_randomized_resolution_contradicts_exact_invariant_support_regression
    (v : PostSwitchInput Z k → Coin → V)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (hmass : 0 < randomizedResidualResolvedMass tiInputMap v w coinWeight) :
    ¬ exactInputInvariantWeightedSupport w := by
  exact
    not_exactInputInvariantWeightedSupport_of_pos_randomizedResidualResolvedMass_tiInputMap
      v w coinWeight hmass

theorem invariant_support_blocks_post_switch_randomized_advantage_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw hsupport

theorem supportwise_unresolved_blocks_post_switch_randomized_advantage_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hunresolved :
      ∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_supportwise_unresolved
      v y w coinWeight h hy hw hunresolved

theorem positive_post_switch_randomized_advantage_witnesses_resolving_coin_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c := by
  exact
    exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
      v y w coinWeight h hy hw hadv

theorem positive_post_switch_randomized_advantage_witnesses_deterministic_coin_slice_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w := by
  exact
    exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
      v y w coinWeight h hy hw hadv

theorem invariant_support_blocks_post_switch_randomized_strict_half_advantage_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass (productWeight w coinWeight) <
      2 * weightedCorrectMass
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw hsupport

theorem strict_half_post_switch_randomized_advantage_witnesses_deterministic_coin_slice_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w := by
  exact
    exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
      v y w coinWeight h hy hw hadv

theorem strict_half_post_switch_randomized_advantage_contradicts_exact_invariant_support_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ¬ exactInputInvariantWeightedSupport w := by
  exact
    not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
      v y w coinWeight h hy hw hadv

theorem no_positive_randomized_advantage_and_exact_invariant_support_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (0 < doubledAdvantage
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h ∧
        exactInputInvariantWeightedSupport w) := by
  exact
    not_pos_doubledAdvantage_randomizedResidual_and_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw

theorem no_strict_half_randomized_advantage_and_exact_invariant_support_regression
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (weightedTotalMass (productWeight w coinWeight) <
          2 * weightedCorrectMass
            (fun xr : PostSwitchInput Z k × Coin =>
              (invariantProjection xr.1, v xr.1 xr.2))
            (fun xr : PostSwitchInput Z k × Coin => y xr.1)
            (productWeight w coinWeight) h ∧
        exactInputInvariantWeightedSupport w) := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_and_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw

end

end Mettapedia.Computability.PNP.PostSwitchRandomizedResidualObstructionRegression
