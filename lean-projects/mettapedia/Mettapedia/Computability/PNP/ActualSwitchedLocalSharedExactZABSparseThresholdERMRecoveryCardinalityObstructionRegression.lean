import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryCardinalityObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def idBitVec1ActualSparseRecoveryCardinality : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k1Nonempty :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec1k1UniformMeasureActualSparseRecoveryCardinality :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_one_sub_pow_inv_bitVec1k1_uniform_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinality
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinality
          q)) :
    1 - (2 ^ (1 + 2 * 1) : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.one_sub_pow_inv_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinality)
      (k := 1)
      (zfeat := idBitVec1ActualSparseRecoveryCardinality)
      h

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1k1_uniform_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinality
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinality
          0) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinality)
      (k := 1)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryCardinality)
      (by
        rw [tsub_pos_iff_lt]
        exact ENNReal.inv_lt_one.2 (by norm_num))

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1k1_uniform_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinality
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          idBitVec1ActualSparseRecoveryCardinality
          0) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_inv_card
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinality)
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (zfeat := idBitVec1ActualSparseRecoveryCardinality)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by
        rw [tsub_pos_iff_lt]
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        exact ENNReal.inv_lt_one.2 (by norm_num))

end Mettapedia.Computability.PNP
