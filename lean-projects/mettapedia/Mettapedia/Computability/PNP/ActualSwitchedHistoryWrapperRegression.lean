import Mettapedia.Computability.PNP.ActualSwitchedHistoryWrapper

/-!
# Regression checks for actual switched-history wrappers

These checks keep the remaining manuscript-facing switched-history route pinned
to the current sharp alternatives: either the actual switched predictor family
already lives in the bounded exact ZAB class, or any genuinely admissible
fielded switching proof still cannot feed a fully expressive exact-visible
family through the wrapper.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

section Positive

variable {Z : Type v} [Fintype Z] {k r clock : ℕ}
variable {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {zfeat : Z → BitVec r}
variable {hist : List (FiniteEvent Bool)} {items : List (V13FieldedStep Bool)}

omit [Fintype Z] in
theorem regression_zabDecisionListData_switchedHistoryExactVisibleCompressionWrapper
    (h : ZABDecisionListData T zfeat) :
    SwitchedHistoryExactVisibleCompressionWrapper
      Bool T (r + 2 * k + 1) hist items := by
  exact h.switchedHistoryExactVisibleCompressionWrapper

theorem regression_zabDecisionListData_switchedHistoryClockedKpolyFiniteLearningWrapper
    (h : ZABDecisionListData T zfeat) :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper
      Bool T (r + 2 * k + 1) clock hist items := by
  exact h.switchedHistoryClockedKpolyFiniteLearningWrapper

end Positive

section Negative

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryExactVisibleCompressionWrapper :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  apply
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
  · trivial
  · exact fullRuleActualSwitchedLocalInterface_surjective Bool 0
  · decide

theorem regression_fullRuleActualSwitchedLocal_no_switchedHistoryClockedKpolyFiniteLearningWrapper :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface Bool 0)
        0
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  apply
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
  · trivial
  · exact fullRuleActualSwitchedLocalInterface_surjective Bool 0
  · decide

end Negative

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
