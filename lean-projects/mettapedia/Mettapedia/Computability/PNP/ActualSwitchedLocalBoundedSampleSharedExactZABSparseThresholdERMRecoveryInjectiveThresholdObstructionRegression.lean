import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMRecoveryInjectiveThresholdObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k1NonemptyActualSparseRecoveryInjectiveThresholdBoundedSample :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

theorem boundedSamplePluginMajorityActualSwitchedLocalInterfaceBitVec1k1SampleBound0_not_surjective :
    ¬ Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 0).predictorFamily.predict := by
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
      (Z := BitVec 1)
      (k := 1)
      (sampleBound := 0)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)

private theorem half_lt_one_sub_pow_inv_of_two_lt_pow_actualSparseRecoveryInjectiveThresholdBoundedSample
    {p : ℕ} (hp : (2 : ℝ≥0∞) < 2 ^ p) :
    ((1 : ℝ≥0∞) / 2) < 1 - (2 ^ p : ℝ≥0∞)⁻¹ := by
  have hhalf : ((1 : ℝ≥0∞) / 2) = 1 - (2 : ℝ≥0∞)⁻¹ := by
    calc
      ((1 : ℝ≥0∞) / 2) = (2 : ℝ≥0∞)⁻¹ := by simp
      _ = 1 - (2 : ℝ≥0∞)⁻¹ := ENNReal.one_sub_inv_two.symm
  rw [hhalf]
  refine (ENNReal.sub_lt_iff_lt_left ?_ ?_).2 ?_
  · simp
  · simp
  have hinv_lt : (2 ^ p : ℝ≥0∞)⁻¹ < (2 : ℝ≥0∞)⁻¹ := by
    simpa using ENNReal.inv_lt_inv' hp
  have hpow_ge_one : (1 : ℝ≥0∞) ≤ 2 ^ p := by
    exact le_of_lt <| lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  have hinv_le_one : (2 ^ p : ℝ≥0∞)⁻¹ ≤ 1 := by
    simpa using ENNReal.inv_le_inv' hpow_ge_one
  calc
    1 = (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 ^ p : ℝ≥0∞)⁻¹ := by
      symm
      exact tsub_add_cancel_of_le hinv_le_one
    _ < (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 : ℝ≥0∞)⁻¹ := by
      exact ENNReal.add_lt_add_left (by simp) hinv_lt
    _ = (2 : ℝ≥0∞)⁻¹ + (1 - (2 ^ p : ℝ≥0∞)⁻¹) := by
      rw [add_comm]

theorem boundedSamplePluginMajorityActualSwitchedLocalInterfaceBitVec1k1SampleBound0_visibleWidth_lt_four_half_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 0)
          idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      (k := 1)
      (r := 1)
      (sampleBound := 0)
      (zfeat := idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      (p := 4)
      h
      (fun _ _ hxy => hxy)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_actualSparseRecoveryInjectiveThresholdBoundedSample
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem boundedSamplePluginMajorityActualSwitchedLocalInterfaceBitVec1k1SampleBound0_one_sub_pow_inv_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 0)
          idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample
          q)) :
    1 - (2 ^ 3 : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_one_sub_pow_inv_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat
      (μ := uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      (k := 1)
      (r := 1)
      (sampleBound := 0)
      (zfeat := idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      h
      (fun _ _ hxy => hxy)
      (by norm_num)

private theorem three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveThresholdBoundedSample :
    (3 : ℝ≥0∞) / 4 < (7 : ℝ≥0∞) / 8 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 6 / 8 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterfaceBitVec1k1SampleBound0_not_nonempty_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 0)
          idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      (k := 1)
      (r := 1)
      (sampleBound := 0)
      (zfeat := idBitVec1ActualSparseRecoveryInjectiveThresholdBoundedSample)
      (fun _ _ hxy => hxy)
      (by norm_num)
      (by
        have hthreshold : 1 - (2 ^ 3 : ℝ≥0∞)⁻¹ = (7 : ℝ≥0∞) / 8 := by
          have hsum : (1 : ℝ≥0∞) = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
            have hinv : ((2 ^ 3 : ℝ≥0∞)⁻¹) = (1 : ℝ≥0∞) / 8 := by
              norm_num
            calc
              (1 : ℝ≥0∞) = (8 : ℝ≥0∞) / 8 := by
                    exact (ENNReal.div_self (by norm_num) (by simp)).symm
              _ = ((7 : ℝ≥0∞) + 1) / 8 := by norm_num
              _ = (7 : ℝ≥0∞) / 8 + (1 : ℝ≥0∞) / 8 := by
                    simpa using
                      (ENNReal.div_add_div_same
                        (a := (7 : ℝ≥0∞))
                        (b := (1 : ℝ≥0∞))
                        (c := (8 : ℝ≥0∞))).symm
              _ = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
                    rw [hinv]
          exact ENNReal.sub_eq_of_eq_add (by simp) hsum
        rw [hthreshold]
        exact three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveThresholdBoundedSample)

end Mettapedia.Computability.PNP
