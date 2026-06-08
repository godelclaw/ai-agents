import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMDataRegression

namespace Mettapedia.Computability.PNP

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMData_surfaceCard_le_bool0_regression :
    Fintype.card (ExactVisiblePostSwitchSurface Bool 0) ≤
      2 * allAffinePointBlockFeatureCount (1 + (0 + 0)) := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression
    with ⟨h⟩
  exact
    h.surfaceCard_le_of_surjective_predict
      (fullRuleActualSwitchedLocalInterface_surjective Bool 0)

def constBitVec0ActualSparseVisibleBudget : BitVec 2 → BitVec 0 := fun _ i => Fin.elim0 i

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_2_0_0_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          constBitVec0ActualSparseVisibleBudget) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (r := 0) (k := 0)
      constBitVec0ActualSparseVisibleBudget
      (by omega)

theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMData_2_0_0_regression :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (r := 0) (k := 0)
      (by omega)

end Mettapedia.Computability.PNP
