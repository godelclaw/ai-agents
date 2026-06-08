import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily

/-!
# Regression checks for the actual switched local family interface

These checks keep the manuscript-shaped local-normal-form surface connected to
the two current outcomes: ZAB ERM identification closes the clocked payload,
while locality alone still permits a full Boolean rule family.
-/

namespace Mettapedia.Computability.PNP

universe u v w

section ConditionalClosure

variable {Z : Type v} [Fintype Z] {r k clock : ℕ}
variable {Index : Type u} {Block : Type w}

theorem regression_actualSwitchedLocal_exactZAB_payload
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    T.clockedKpolyFiniteLearningPayload_of_eq_exactZABDecisionListERMFamily
      zfeat samples hT

theorem regression_actualSwitchedLocal_bitVecZAB_payload
    [Fintype (BitVec r)]
    (T : ActualSwitchedLocalInterface (BitVec r) k Index Block)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    T.clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily
      samples hT

end ConditionalClosure

section LocalityOnlyObstruction

variable {Z : Type v} [Fintype Z] {k s clock : ℕ}

theorem regression_fullRuleActualSwitchedLocal_no_cover
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (fullRuleActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    fullRuleActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem regression_actualSwitchedLocal_not_forall_payload
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} {Block : Type v}
        (T : ActualSwitchedLocalInterface Z k Index Block),
        ClockedKpolyFiniteLearningPayload T.predictorFamily s clock) := by
  exact
    actualSwitchedLocalInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

end LocalityOnlyObstruction

end Mettapedia.Computability.PNP
