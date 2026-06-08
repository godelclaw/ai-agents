import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryThresholdWidthObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def idBitVec1ActualSparseRecoveryThresholdWidth : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k1NonemptyThresholdWidth :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

private theorem half_lt_one_sub_pow_inv_of_two_lt_pow {p : ℕ}
    (hp : (2 : ℝ≥0∞) < 2 ^ p) :
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

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_visibleWidth_lt_four_bitVec1k1_uniform_half_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryThresholdWidth
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.visibleWidth_lt_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth)
      (k := 1)
      (zfeat := idBitVec1ActualSparseRecoveryThresholdWidth)
      (p := 4)
      h
      (half_lt_one_sub_pow_inv_of_two_lt_pow (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1k1_uniform_half_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryThresholdWidth
          ((1 : ℝ≥0∞) / 2)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth)
      (k := 1)
      (r := 1)
      (p := 3)
      (zfeat := idBitVec1ActualSparseRecoveryThresholdWidth)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1k1_uniform_half_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          idBitVec1ActualSparseRecoveryThresholdWidth
          ((1 : ℝ≥0∞) / 2)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryThresholdWidth)
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (p := 3)
      (zfeat := idBitVec1ActualSparseRecoveryThresholdWidth)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

end Mettapedia.Computability.PNP
