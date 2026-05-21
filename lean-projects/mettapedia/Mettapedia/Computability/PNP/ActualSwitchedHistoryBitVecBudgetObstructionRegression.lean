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

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryExactVisibleCompressionWrapper_budget_lt :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        3
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (s := 3)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by norm_num)

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryClockedKpolyFiniteLearningWrapper_budget_lt :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        3
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (s := 3) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by norm_num)

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

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryExactVisibleCompressionWrapper_two_le_visibleWidth :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (2 + 2 * 0 + 1)
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_two_le_visibleWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
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

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryClockedKpolyFiniteLearningWrapper_two_le_visibleWidth :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (2 + 2 * 0 + 1)
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_two_le_visibleWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by norm_num)

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryExactVisibleCompressionWrapper_le_fullWidthBudget :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryClockedKpolyFiniteLearningWrapper_le_fullWidthBudget :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
