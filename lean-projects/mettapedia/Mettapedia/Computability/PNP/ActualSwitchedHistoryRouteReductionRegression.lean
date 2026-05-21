import Mettapedia.Computability.PNP.ActualSwitchedHistoryRouteReduction

/-!
# Regression checks for actual switched-history route reduction

These checks keep the remaining manuscript-facing switched-history route tied to
the existing finite-image obligations, rather than letting it drift into a new
bridge principle.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

theorem regression_fullRule_switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget :
    SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) ↔
      ExactVisibleCompressionTarget
        (Z := Bool) (k := 0)
        (Index := ExactVisibleRule Bool 0)
        (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily
        0 := by
  exact
    switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget_of_true_fieldedSwitching
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)

theorem regression_fullRule_switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) ↔
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorCover 1 := by
  simpa using
    (switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial))

theorem regression_fullRule_switchedHistoryExactVisibleCompressionWrapper_iff_finiteIndexRepresentativeCover :
    SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) ↔
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FiniteIndexRepresentativeCover 1 := by
  simpa using
    (switchedHistoryExactVisibleCompressionWrapper_iff_finiteIndexRepresentativeCover_of_true_fieldedSwitching
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial))

theorem regression_fullRule_switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorQuotient :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) ↔
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorQuotient 1 := by
  simpa using
    (switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorQuotient_of_true_fieldedSwitching
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial))

theorem regression_not_switchedHistoryExactVisibleCompressionWrapper_of_not_finitePredictorCover :
    ¬ (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorCover 1 →
      ¬ SwitchedHistoryExactVisibleCompressionWrapper
          Bool
          (fullRuleActualSwitchedLocalInterface Bool 0)
          0
          ([] : List (FiniteEvent Bool))
          ([] : List (V13FieldedStep Bool)) := by
  intro hnot
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_not_finitePredictorCover
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (by simpa using hnot)

theorem regression_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_not_finitePredictorCover :
    ¬ (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorCover 1 →
      ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
          Bool
          (fullRuleActualSwitchedLocalInterface Bool 0)
          0
          0
          ([] : List (FiniteEvent Bool))
          ([] : List (V13FieldedStep Bool)) := by
  intro hnot
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_not_finitePredictorCover
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (by simpa using hnot)

theorem regression_not_switchedHistoryExactVisibleCompressionWrapper_of_not_finiteIndexRepresentativeCover :
    ¬ (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FiniteIndexRepresentativeCover 1 →
      ¬ SwitchedHistoryExactVisibleCompressionWrapper
          Bool
          (fullRuleActualSwitchedLocalInterface Bool 0)
          0
          ([] : List (FiniteEvent Bool))
          ([] : List (V13FieldedStep Bool)) := by
  intro hnot
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_not_finiteIndexRepresentativeCover
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (by simpa using hnot)

theorem regression_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_not_finitePredictorQuotient :
    ¬ (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily.FinitePredictorQuotient 1 →
      ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
          Bool
          (fullRuleActualSwitchedLocalInterface Bool 0)
          0
          0
          ([] : List (FiniteEvent Bool))
          ([] : List (V13FieldedStep Bool)) := by
  intro hnot
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_not_finitePredictorQuotient
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (s := 0) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (by simpa using hnot)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
