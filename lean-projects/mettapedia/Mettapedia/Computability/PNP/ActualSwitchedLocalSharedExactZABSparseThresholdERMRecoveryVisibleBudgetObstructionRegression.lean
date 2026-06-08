import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryVisibleBudgetObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def idBitVec1ActualSparseRecoveryVisibleBudget : BitVec 1 → BitVec 1 := fun x => x

def constBitVec0ActualSparseRecoveryVisibleBudget : BitVec 2 → BitVec 0 := fun _ i => Fin.elim0 i

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyActualSparseRecoveryVisibleBudget :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

local instance exactVisiblePostSwitchSurfaceBitVec2k0NonemptyActualSparseRecoveryVisibleBudget :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 2) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec1k0UniformMeasureActualSparseRecoveryVisibleBudget :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  PMF.uniformOfFintype _

noncomputable def bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget :
    PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0) :=
  PMF.uniformOfFintype _

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_visibleWidth_le_bitVec1k0r1_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k0UniformMeasureActualSparseRecoveryVisibleBudget
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryVisibleBudget
          (0 : ℝ≥0∞))) :
    1 ≤ 2 * 1 + 2 * 0 + 1 := by
  exact
    ActualSwitchedLocalInterface.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
      (n := 1)
      (k := 0)
      (r := 1)
      (μ := bitVec1k0UniformMeasureActualSparseRecoveryVisibleBudget)
      (zfeat := idBitVec1ActualSparseRecoveryVisibleBudget)
      (q := (0 : ℝ≥0∞))
      h

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec2k0r0_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          constBitVec0ActualSparseRecoveryVisibleBudget
          (0 : ℝ≥0∞)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget)
      (zfeat := constBitVec0ActualSparseRecoveryVisibleBudget)
      (q := (0 : ℝ≥0∞))
      (by omega)

theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_bitVec2k0r0_regression :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat
            (0 : ℝ≥0∞)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget)
      (q := (0 : ℝ≥0∞))
      (by omega)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec2k0r0sampleBound4_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 2) 0 4)
          constBitVec0ActualSparseRecoveryVisibleBudget
          (0 : ℝ≥0∞)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (sampleBound := 4)
      (μ := bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget)
      (zfeat := constBitVec0ActualSparseRecoveryVisibleBudget)
      (q := (0 : ℝ≥0∞))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by omega)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_bitVec2k0r0sampleBound4_regression :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget
            (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 2) 0 4)
            zfeat
            (0 : ℝ≥0∞)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (sampleBound := 4)
      (μ := bitVec2k0UniformMeasureActualSparseRecoveryVisibleBudget)
      (q := (0 : ℝ≥0∞))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by omega)

end Mettapedia.Computability.PNP
