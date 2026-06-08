import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure

/-!
# Regression checks for actual switched local structure beyond locality

These checks keep the strengthened-interface results visible:
bounded local code data and concrete ZAB decision-list data both close the
finite predictor-image target, and both rule out the full-rule local
counterexample below the exact visible truth-table budget.
-/

namespace Mettapedia.Computability.PNP

universe u v w

section BoundedCodeClosure

variable {Z : Type v} {k s clock : ℕ}
variable {Index : Type u} {Block : Type w}

theorem regression_actualSwitchedLocal_bitCode_cover
    {T : ActualSwitchedLocalInterface Z k Index Block}
    (h : ActualSwitchedLocalInterface.BitCodeData T s) :
    T.predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact h.finitePredictorCover

theorem regression_actualSwitchedLocal_bitCode_payload
    [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    (h : ActualSwitchedLocalInterface.BitCodeData T s) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  exact h.clockedKpolyFiniteLearningPayload

end BoundedCodeClosure

section ZABClosure

variable {Z : Type v} {r k clock : ℕ}
variable {Index : Type u} {Block : Type w}

theorem regression_actualSwitchedLocal_zab_cover
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {zfeat : Z → BitVec r}
    (h : ActualSwitchedLocalInterface.ZABDecisionListData T zfeat) :
    T.predictorFamily.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.finitePredictorCover

theorem regression_actualSwitchedLocal_zab_payload
    [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {zfeat : Z → BitVec r}
    (h : ActualSwitchedLocalInterface.ZABDecisionListData T zfeat) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily (r + 2 * k + 1) clock := by
  exact h.clockedKpolyFiniteLearningPayload

theorem regression_actualSwitchedLocal_exactZAB_ERM_eq_to_zab_cover
    {T : ActualSwitchedLocalInterface Z k Index Block}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    T.predictorFamily.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact
    (ActualSwitchedLocalInterface.zabDecisionListData_of_eq_exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) (Index := Index) (Block := Block)
      T zfeat samples hT).finitePredictorCover

theorem regression_actualSwitchedLocal_exactZAB_ERM_eq_to_bitCode_payload
    [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    (ActualSwitchedLocalInterface.bitCodeData_of_eq_exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) (Index := Index) (Block := Block)
      T zfeat samples hT).clockedKpolyFiniteLearningPayload

end ZABClosure

section BitVecERMClosure

variable {r k clock : ℕ}
variable {Index : Type u} {Block : Type w}

theorem regression_actualSwitchedLocal_bitVecZAB_ERM_eq_to_zab_cover
    {T : ActualSwitchedLocalInterface (BitVec r) k Index Block}
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    T.predictorFamily.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact
    (ActualSwitchedLocalInterface.zabDecisionListData_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (Index := Index) (Block := Block)
      T samples hT).finitePredictorCover

theorem regression_actualSwitchedLocal_bitVecZAB_ERM_eq_to_bitCode_payload
    [Fintype (BitVec r)]
    {T : ActualSwitchedLocalInterface (BitVec r) k Index Block}
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    (ActualSwitchedLocalInterface.bitCodeData_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (Index := Index) (Block := Block)
      T samples hT).clockedKpolyFiniteLearningPayload

end BitVecERMClosure

section FullRuleExclusions

variable {Z : Type v} [Fintype Z] {r k s : ℕ}

theorem regression_fullRuleActualSwitchedLocal_not_bitCodeData
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (fullRuleActualSwitchedLocalInterface Z k) s) := by
  exact
    fullRuleActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem regression_fullRuleActualSwitchedLocal_not_zabDecisionListData
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

end FullRuleExclusions

end Mettapedia.Computability.PNP
