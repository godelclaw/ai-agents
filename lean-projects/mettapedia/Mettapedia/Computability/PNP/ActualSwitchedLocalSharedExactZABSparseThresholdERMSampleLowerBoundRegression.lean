import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMSampleLowerBound
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMWidthCharacterizationRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

theorem sparseThresholdPointBlockBudgetPow_lt_sampleSize_of_gap_bitVec_1_1_0_17_regression :
    2 ^ (2 * (1 + (0 + 0)) + 1) < 17 := by
  refine
    sparseThresholdPointBlockBudgetPow_lt_sampleSize_of_gap_bitVec
      (n := 1) (r := 1) (k := 0) (m := 17) ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bitVec]
    norm_num [allAffinePointBlockFeatureCount_eq]

theorem fullRuleActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData_1_1_0_17_regression :
    2 ^ (2 * (1 + (0 + 0)) + 1) < 17 := by
  rcases
    fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_1_1_regression
      with ⟨zfeat, hdata⟩
  refine
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 1) (r := 1) (k := 0) (m := 17)
      (zfeat := zfeat)
      hdata ?_ ?_ ?_
  · decide
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bitVec]
    norm_num [allAffinePointBlockFeatureCount_eq]

end Mettapedia.Computability.PNP
