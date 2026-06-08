import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMRecoverySampleBoundObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

def constBitVec0BoundedSampleRecoverySampleBound : BitVec 1 → BitVec 0 := fun _ i => Fin.elim0 i

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyBoundedSampleRecoverySampleBound :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_1_1_0_17_regression
    {zfeat : BitVec 1 → BitVec 1}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 17)
          zfeat
          0)) :
    2 ^ (2 * (1 + (0 + 0)) + 1) < 17 := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
      (n := 1) (r := 1) (k := 0) (sampleBound := 17)
      (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
      (zfeat := zfeat)
      (q := 0)
      h
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_1_0_0_3_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 3)
          constBitVec0BoundedSampleRecoverySampleBound
          0) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_sampleBound_le_visibleWidthBudget
      (n := 1) (r := 0) (k := 0) (sampleBound := 3)
      (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
      (zfeat := constBitVec0BoundedSampleRecoverySampleBound)
      (q := 0)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])
      (by norm_num)

end Mettapedia.Computability.PNP
