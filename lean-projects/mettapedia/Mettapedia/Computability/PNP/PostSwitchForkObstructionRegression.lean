import Mettapedia.Computability.PNP.PostSwitchForkObstruction

/-!
# Regression checks for the exact post-switch side-channel fork

These wrappers pin the manuscript-specific consequence of the resolution-demand
obstruction: the exact `(z, a_i, b)` side channel can only buy advantage on mass
carried by nonzero `a_i` columns.
-/

namespace Mettapedia.Computability.PNP.PostSwitchForkObstructionRegression

open Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ} [Fintype Z]

theorem claimed_b_side_channel_gap_forces_nonzero_column_mass_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool) (δ : ℕ)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hδ :
      δ ≤ doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    δ ≤ sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  exact nonzeroColumnMass_ge_of_le_doubledAdvantage_invariantProjection_with_b
    y w h δ hy hw hδ

theorem positive_b_side_channel_advantage_forces_positive_nonzero_column_mass_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  exact
    pos_nonzeroColumnMass_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

theorem positive_nonzero_column_mass_exposes_support_point_regression
    (w : PostSwitchInput Z k → ℕ)
    (hmass :
      0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  exact exists_nonzeroColumn_of_pos_nonzeroColumnMass w hmass

theorem positive_b_side_channel_advantage_exposes_b_resolving_input_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b := by
  exact
    exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

theorem positive_b_side_channel_advantage_exposes_nonzero_column_input_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  exact
    exists_nonzeroColumn_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

theorem strict_half_b_side_channel_advantage_forces_positive_nonzero_column_mass_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  exact
    pos_nonzeroColumnMass_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
      y w h hy hw hadv

theorem strict_half_b_side_channel_advantage_exposes_b_resolving_input_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b := by
  exact
    exists_b_resolving_input_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
      y w h hy hw hadv

theorem strict_half_b_side_channel_advantage_exposes_nonzero_column_input_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  exact
    exists_nonzeroColumn_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
      y w h hy hw hadv

theorem zero_nonzero_column_mass_blocks_b_side_channel_advantage_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hmass : sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0) :
    ¬ 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
  exact not_pos_doubledAdvantage_invariantProjection_with_b_of_zero_nonzeroColumnMass
    y w h hy hw hmass

theorem invariant_weighted_support_has_zero_nonzero_column_mass_regression
    (w : PostSwitchInput Z k → ℕ)
    (hsupport : exactInputInvariantWeightedSupport w) :
    sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0 := by
  exact nonzeroColumnMass_eq_zero_of_exactInputInvariantWeightedSupport w hsupport

theorem zero_nonzero_column_mass_blocks_strict_half_b_side_channel_advantage_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hmass : sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_zero_nonzeroColumnMass
      y w h hy hw hmass

theorem positive_nonzero_column_mass_contradicts_invariant_support_regression
    (w : PostSwitchInput Z k → ℕ)
    (hmass :
      0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w) :
    ¬ exactInputInvariantWeightedSupport w := by
  exact not_exactInputInvariantWeightedSupport_of_pos_nonzeroColumnMass w hmass

theorem invariant_support_blocks_b_side_channel_advantage_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
  exact
    not_pos_doubledAdvantage_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hsupport

theorem invariant_support_blocks_strict_half_b_side_channel_advantage_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hsupport

theorem positive_b_side_channel_advantage_refutes_invariant_support_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ¬ exactInputInvariantWeightedSupport w := by
  exact
    not_exactInputInvariantWeightedSupport_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

theorem strict_half_b_side_channel_advantage_refutes_invariant_support_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ¬ exactInputInvariantWeightedSupport w := by
  exact
    not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
      y w h hy hw hadv

theorem no_positive_advantage_and_invariant_support_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ∧
        exactInputInvariantWeightedSupport w) := by
  exact not_pos_doubledAdvantage_and_exactInputInvariantWeightedSupport y w h hy hw

theorem no_strict_half_advantage_and_invariant_support_regression
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (weightedTotalMass w <
          2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h ∧
        exactInputInvariantWeightedSupport w) := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_and_exactInputInvariantWeightedSupport
      y w h hy hw

end

end Mettapedia.Computability.PNP.PostSwitchForkObstructionRegression
