import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMVisibleBudgetObstruction
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData_2_1_0_4_regression
    {zfeat : BitVec 2 → BitVec 1}
    (hdata :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 2) 0 4)
          zfeat)) :
    2 ≤ 2 * 1 + 2 * 0 + 1 := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 2) (r := 1) (k := 0) (sampleBound := 4)
      (zfeat := zfeat)
      hdata
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)

def constBitVec0BoundedSampleVisibleBudget : BitVec 2 → BitVec 0 := fun _ i => Fin.elim0 i

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_2_0_0_4_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 2) 0 4)
          constBitVec0BoundedSampleVisibleBudget) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (r := 0) (k := 0) (sampleBound := 4)
      (zfeat := constBitVec0BoundedSampleVisibleBudget)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by omega)

end Mettapedia.Computability.PNP
