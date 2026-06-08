import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMBitCode
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMDataRegression

namespace Mettapedia.Computability.PNP

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMData_bitCodeData_bool0_regression :
    Nonempty
      (ActualSwitchedLocalInterface.BitCodeData
        (fullRuleActualSwitchedLocalInterface Bool 0)
        (2 * allAffinePointBlockFeatureCount (1 + (0 + 0)))) := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression
    with ⟨h⟩
  exact ⟨h.bitCodeData⟩

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMData_finitePredictorCover_bool0_regression :
    (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorCover
      (2 ^ (2 * allAffinePointBlockFeatureCount (1 + (0 + 0)))) := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression
    with ⟨h⟩
  exact h.finitePredictorCover

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMData_clockedKpolyFiniteLearningPayload_bool0_regression :
    ClockedKpolyFiniteLearningPayload
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily
      (2 * allAffinePointBlockFeatureCount (1 + (0 + 0)))
      0 := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression
    with ⟨h⟩
  exact h.clockedKpolyFiniteLearningPayload (clock := 0)

end Mettapedia.Computability.PNP
