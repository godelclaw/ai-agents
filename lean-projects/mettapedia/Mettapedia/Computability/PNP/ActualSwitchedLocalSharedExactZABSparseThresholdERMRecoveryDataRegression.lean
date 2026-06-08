import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMDataRegression
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

def bool0VisiblePointActualSparse :
    ExactVisiblePostSwitchSurface Bool 0 :=
  ⟨false, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

noncomputable def bool0PureMeasureActualSparse : PMF (ExactVisiblePostSwitchSurface Bool 0) :=
  PMF.pure bool0VisiblePointActualSparse

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bool0_regression :
    Nonempty
      (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
        bool0PureMeasureActualSparse
        (fullRuleActualSwitchedLocalInterface Bool 0)
        boolToBitVec1ActualSparse
        ⊤) := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression
    with ⟨hdata⟩
  refine ⟨{ data := hdata, agreement_le := ?_ }⟩
  intro i c
  simp

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_clockedKpolyFiniteLearningPayload_bool0_regression :
    ClockedKpolyFiniteLearningPayload
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily
      (2 * allAffinePointBlockFeatureCount (1 + (0 + 0)))
      0 := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bool0_regression
    with ⟨h⟩
  exact h.clockedKpolyFiniteLearningPayload (clock := 0)

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_const_bool0_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bool0PureMeasureActualSparse
          (fullRuleActualSwitchedLocalInterface Bool 0)
          constBitVec1ActualSparse
          0) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_not_injective_zfeat
      (μ := bool0PureMeasureActualSparse)
      (q := 0)
      constBitVec1ActualSparse
      constBitVec1ActualSparse_not_injective

end Mettapedia.Computability.PNP
