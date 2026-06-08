import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleBound
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData_1_1_0_17_regression
    {zfeat : BitVec 1 → BitVec 1}
    (hdata :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 17)
          zfeat)) :
    2 ^ (2 * (1 + (0 + 0)) + 1) < 17 := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 1) (r := 1) (k := 0) (sampleBound := 17)
      (zfeat := zfeat)
      hdata
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_visibleSurfaceCard_le_of_width_le_1_1_0_17_regression :
    2 ^ (2 * (1 + (0 + 0)) + 1) < 17 := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_visibleSurfaceCard_le_of_width_le
      (n := 1) (r := 1) (k := 0) (sampleBound := 17)
      (by omega)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by decide)
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_1_0_0_3_regression
    (zfeat : BitVec 1 → BitVec 0) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 3)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_sampleBound_le_visibleWidthBudget
      (n := 1) (r := 0) (k := 0) (sampleBound := 3)
      (zfeat := zfeat)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num [allAffinePointBlockFeatureCount_eq])
      (by norm_num)

end Mettapedia.Computability.PNP
