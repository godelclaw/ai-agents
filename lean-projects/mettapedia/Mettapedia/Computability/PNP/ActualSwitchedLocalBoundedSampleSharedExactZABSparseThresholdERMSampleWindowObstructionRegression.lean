import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleWindowObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

def constBitVec0BoundedSampleSampleWindow : BitVec 1 → BitVec 0 := fun _ i => Fin.elim0 i

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyBoundedSampleSampleWindow :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_sampleWindow_gap_regression
    {zfeat : BitVec 1 → BitVec 0}
    (hdata :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 3)
          zfeat)) :
    3 < 2 ^ (1 + 2 * 0) ∨ 2 ^ (2 * (1 + (0 + 0)) + 1) < 3 := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_sampleBound_lt_visibleSurfaceCard_or_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 1)
      (r := 0)
      (k := 0)
      (sampleBound := 3)
      (zfeat := zfeat)
      hdata
      (by norm_num)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_bitVec1k0r0sampleBound3_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 3)
          constBitVec0BoundedSampleSampleWindow) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_visibleSurfaceCard_le_sampleBound_of_sampleBound_le_visibleWidthBudget
      (n := 1)
      (r := 0)
      (k := 0)
      (sampleBound := 3)
      (zfeat := constBitVec0BoundedSampleSampleWindow)
      (by norm_num)
      (by norm_num)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])
      (by norm_num)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1k0r0sampleBound3_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 3)
          constBitVec0BoundedSampleSampleWindow
          0) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_visibleSurfaceCard_sampleWindow
      (n := 1)
      (r := 0)
      (k := 0)
      (sampleBound := 3)
      (zfeat := constBitVec0BoundedSampleSampleWindow)
      (μ := PMF.uniformOfFintype (ExactVisiblePostSwitchSurface (BitVec 1) 0))
      (q := 0)
      (by norm_num)
      (by norm_num)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])
      (by norm_num)

end Mettapedia.Computability.PNP
