import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMCharacterization

namespace Mettapedia.Computability.PNP

def boolToBitVec1ActualSparseChar : Bool → BitVec 1 := fun b _ => b

theorem boolToBitVec1ActualSparseChar_injective :
    Function.Injective boolToBitVec1ActualSparseChar := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

def constBitVec1ActualSparseChar : Bool → BitVec 1 := fun _ _ => false

theorem constBitVec1ActualSparseChar_not_injective :
    ¬ Function.Injective constBitVec1ActualSparseChar := by
  intro hinj
  have h : false = true := hinj (a₁ := false) (a₂ := true) rfl
  exact Bool.false_ne_true h

def exactVisiblePostSwitchSurfaceBool0EquivActualSparseChar :
    ExactVisiblePostSwitchSurface Bool 0 ≃ Bool where
  toFun u := u.z
  invFun z := ⟨z, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  left_inv := by
    intro u
    cases u with
    | mk z a b =>
        have ha : (fun i => Fin.elim0 i : BitVec 0) = a := Subsingleton.elim _ _
        have hb : (fun i => Fin.elim0 i : BitVec 0) = b := Subsingleton.elim _ _
        cases ha
        cases hb
        rfl
  right_inv := by
    intro z
    rfl

theorem card_exactVisiblePostSwitchSurface_bool0_actualSparseChar :
    Fintype.card (ExactVisiblePostSwitchSurface Bool 0) = 2 := by
  simpa using Fintype.card_congr exactVisiblePostSwitchSurfaceBool0EquivActualSparseChar

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat_bool0_regression :
    Nonempty
      (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Bool 0)
        boolToBitVec1ActualSparseChar) ↔
      Function.Injective boolToBitVec1ActualSparseChar := by
  refine
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat
      (Z := Bool) (r := 1) (k := 0) (m := 9) boolToBitVec1ActualSparseChar ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bool0_actualSparseChar]
    norm_num [allAffinePointBlockFeatureCount_eq]

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression :
    Nonempty
      (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Bool 0)
        boolToBitVec1ActualSparseChar) := by
  exact
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat_bool0_regression.2
      boolToBitVec1ActualSparseChar_injective

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_const_bool0_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface Bool 0)
          constBitVec1ActualSparseChar) := by
  intro h
  exact
    constBitVec1ActualSparseChar_not_injective <|
      (ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat
        (Z := Bool) (r := 1) (k := 0) (m := 9) constBitVec1ActualSparseChar
        (by decide)
        (by
          rw [card_exactVisiblePostSwitchSurface_bool0_actualSparseChar]
          norm_num [allAffinePointBlockFeatureCount_eq])).1 h

end Mettapedia.Computability.PNP
