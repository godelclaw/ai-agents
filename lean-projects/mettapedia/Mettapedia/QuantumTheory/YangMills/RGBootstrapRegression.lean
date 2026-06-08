import Mettapedia.QuantumTheory.YangMills.RGBootstrap

/-!
# Yang-Mills RG Bootstrap Regression

Regression wrappers for the extended-extraction numerical contraction audit and
the affine bootstrap invariant.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace RGBootstrapRegression

theorem irrelevant_scale_two_sixteen_regression :
    irrelevantScale 2 16 = (1 : ℝ) / 8192 := by
  exact irrelevantScale_two_sixteen

theorem irrelevant_scale_two_four_regression :
    irrelevantScale 2 4 = (1 : ℝ) / 2 := by
  exact irrelevantScale_two_four

theorem irrelevant_scale_two_fourteen_regression :
    irrelevantScale 2 14 = (1 : ℝ) / 2048 := by
  exact irrelevantScale_two_fourteen

theorem irrelevant_scale_two_fifteen_regression :
    irrelevantScale 2 15 = (1 : ℝ) / 4096 := by
  exact irrelevantScale_two_fifteen

theorem irrelevant_scale_general_threshold_regression
    {b dmax : ℕ} (hdmax : 3 ≤ dmax) :
    irrelevantScale b dmax = ((b : ℝ) ^ (dmax - 3))⁻¹ := by
  exact irrelevantScale_eq_inv_pow_of_three_le hdmax

theorem rg_contraction_exact_threshold_regression
    {C : ℝ} {b dmax : ℕ} (hb : 0 < b) (hdmax : 3 ≤ dmax) :
    HasExtendedExtractionContraction C b dmax ↔
      0 ≤ C ∧ C < (b : ℝ) ^ (dmax - 3) := by
  exact rgContraction_iff_constant_lt_pow_of_pos_of_three_le hb hdmax

theorem rg_contraction_forces_exact_threshold_regression
    {C : ℝ} {b dmax : ℕ} (hb : 0 < b) (hdmax : 3 ≤ dmax)
    (h : HasExtendedExtractionContraction C b dmax) :
    C < (b : ℝ) ^ (dmax - 3) := by
  exact rgContraction_forces_constant_lt_pow_of_pos_of_three_le hb hdmax h

theorem advertised_constant_not_contraction_below_threshold_regression
    {b dmax : ℕ} (hb : 0 < b) (hdmax : 3 ≤ dmax)
    (hpow : (b : ℝ) ^ (dmax - 3) ≤ 2224) :
    ¬ HasExtendedExtractionContraction 2224 b dmax := by
  exact not_rgContraction_2224_of_pow_le_of_pos_of_three_le hb hdmax hpow

theorem irrelevant_scale_two_general_threshold_regression
    {dmax : ℕ} (hdmax : 3 ≤ dmax) :
    irrelevantScale 2 dmax = ((2 : ℝ) ^ (dmax - 3))⁻¹ := by
  exact irrelevantScale_two_eq_inv_pow_of_three_le hdmax

theorem rg_contraction_two_exact_threshold_regression
    {C : ℝ} {dmax : ℕ} (hdmax : 3 ≤ dmax) :
    HasExtendedExtractionContraction C 2 dmax ↔
      0 ≤ C ∧ C < (2 : ℝ) ^ (dmax - 3) := by
  exact rgContraction_two_iff_constant_lt_pow_of_three_le hdmax

theorem rg_contraction_two_forces_exact_threshold_regression
    {C : ℝ} {dmax : ℕ} (hdmax : 3 ≤ dmax)
    (h : HasExtendedExtractionContraction C 2 dmax) :
    C < (2 : ℝ) ^ (dmax - 3) := by
  exact rgContraction_two_forces_constant_lt_pow_of_three_le hdmax h

theorem advertised_extended_extraction_contraction_regression :
    HasExtendedExtractionContraction 2224 2 16 := by
  exact rgContraction_2224_two_sixteen

theorem raw_fifteen_extraction_contraction_regression :
    HasExtendedExtractionContraction 2224 2 15 := by
  exact rgContraction_2224_two_fifteen

theorem advertised_extended_extraction_gain_exact_regression :
    (2224 : ℝ) * irrelevantScale 2 16 = (139 : ℝ) / 512 := by
  exact rgGain_2224_two_sixteen_eq

theorem advertised_extended_extraction_gain_lt_one_third_regression :
    (2224 : ℝ) * irrelevantScale 2 16 < (1 : ℝ) / 3 := by
  exact rgGain_2224_two_sixteen_lt_one_third

theorem naive_marginal_extraction_not_contraction_regression :
    ¬ HasExtendedExtractionContraction 2224 2 4 := by
  exact not_rgContraction_2224_two_four

theorem naive_marginal_extraction_gain_exact_regression :
    (2224 : ℝ) * irrelevantScale 2 4 = 1112 := by
  exact rgGain_2224_two_four_eq

theorem near_extended_extraction_gain_exact_regression :
    (2224 : ℝ) * irrelevantScale 2 14 = (139 : ℝ) / 128 := by
  exact rgGain_2224_two_fourteen_eq

theorem raw_fifteen_extraction_gain_exact_regression :
    (2224 : ℝ) * irrelevantScale 2 15 = (139 : ℝ) / 256 := by
  exact rgGain_2224_two_fifteen_eq

theorem near_extended_extraction_constant_threshold_regression
    {C : ℝ} (h : HasExtendedExtractionContraction C 2 14) :
    C < 2048 := by
  exact rgContraction_two_fourteen_forces_constant_lt_2048 h

theorem near_extended_extraction_not_contraction_regression :
    ¬ HasExtendedExtractionContraction 2224 2 14 := by
  exact not_rgContraction_2224_two_fourteen

theorem near_extended_extraction_large_constant_not_contraction_regression
    {C : ℝ} (hC : 2048 ≤ C) :
    ¬ HasExtendedExtractionContraction C 2 14 := by
  exact not_rgContraction_two_fourteen_of_ge_2048 hC

theorem lower_depth_large_constant_not_contraction_regression
    {C : ℝ} {dmax : ℕ} (hC : 2048 ≤ C) (hdmax : dmax ≤ 14) :
    ¬ HasExtendedExtractionContraction C 2 dmax := by
  exact not_rgContraction_two_of_ge_2048_of_dmax_le_fourteen hC hdmax

theorem lower_depth_extraction_not_contraction_regression
    {dmax : ℕ} (hdmax : dmax ≤ 14) :
    ¬ HasExtendedExtractionContraction 2224 2 dmax := by
  exact not_rgContraction_2224_two_of_dmax_le_fourteen hdmax

theorem bounded_constant_extended_extraction_contraction_regression
    {C : ℝ} (hCnonneg : 0 ≤ C) (hC : C ≤ 2224) :
    HasExtendedExtractionContraction C 2 16 := by
  exact rgContraction_of_nonneg_le_2224_two_sixteen hCnonneg hC

theorem contraction_audit_gives_gain_regression
    {C scale : ℝ} (h : HasRGContraction C scale) :
    IsRGContractionGain (C * scale) := by
  exact h.gain

theorem affine_rg_step_bound_regression
    {κ ε B : ℝ} {a : ℕ → ℝ}
    (hstep : AffineRGStepBound κ ε a)
    (hκ_nonneg : 0 ≤ κ)
    (hε : ε ≤ (1 - κ) * B)
    (h0 : a 0 ≤ B) :
    ∀ n : ℕ, a n ≤ B := by
  exact hstep.bound_by_invariant_interval hκ_nonneg hε h0

theorem affine_rg_step_le_envelope_regression
    {κ ε : ℝ} {a : ℕ → ℝ}
    (hstep : AffineRGStepBound κ ε a)
    (hκ_nonneg : 0 ≤ κ) :
    ∀ n : ℕ, a n ≤ affineRGEnvelope κ ε (a 0) n := by
  exact hstep.le_affineRGEnvelope hκ_nonneg

theorem affine_rg_envelope_zero_error_regression
    (κ a0 : ℝ) :
    ∀ n : ℕ, affineRGEnvelope κ 0 a0 n = κ ^ n * a0 := by
  exact affineRGEnvelope_zero_error κ a0

theorem affine_rg_step_geometric_zero_error_regression
    {κ : ℝ} {a : ℕ → ℝ}
    (hstep : AffineRGStepBound κ 0 a)
    (hκ_nonneg : 0 ≤ κ) :
    ∀ n : ℕ, a n ≤ κ ^ n * a 0 := by
  exact hstep.bound_by_geometric_of_zero_error hκ_nonneg

end RGBootstrapRegression
end YangMills
end QuantumTheory
end Mettapedia
