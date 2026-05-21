import Mettapedia.Computability.PNP.ActualSwitchedHistoryBitVecBudgetObstruction

/-!
# Regression checks for switched-history bitvector budget obstructions
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

theorem regression_switchedHistoryBudget_lt_surfaceCard_bitVec2 :
    2 + 2 * 0 + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0) := by
  exact
    switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
      (n := 2) (k := 0) (r := 2) (by norm_num) (by norm_num)

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryExactVisibleCompressionWrapper_sameWidth :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (2 + 2 * 0 + 1)
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (r := 2)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by norm_num)
      (by norm_num)

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryClockedKpolyFiniteLearningWrapper_sameWidth :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (2 + 2 * 0 + 1)
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (r := 2) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by norm_num)
      (by norm_num)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
