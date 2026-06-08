import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMData

namespace Mettapedia.Computability.PNP

def boolToBitVec1ActualSparse : Bool → BitVec 1 := fun b _ => b

theorem boolToBitVec1ActualSparse_injective : Function.Injective boolToBitVec1ActualSparse := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

def constBitVec1ActualSparse : Bool → BitVec 1 := fun _ _ => false

theorem constBitVec1ActualSparse_not_injective : ¬ Function.Injective constBitVec1ActualSparse := by
  intro hinj
  have h : false = true := hinj (a₁ := false) (a₂ := true) rfl
  exact Bool.false_ne_true h

def exactVisiblePostSwitchSurfaceBool0EquivActualSparse :
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

theorem card_exactVisiblePostSwitchSurface_bool0_actualSparse :
    Fintype.card (ExactVisiblePostSwitchSurface Bool 0) = 2 := by
  simpa using Fintype.card_congr exactVisiblePostSwitchSurfaceBool0EquivActualSparse

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_bool0_regression :
    Nonempty
      (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Bool 0)
        boolToBitVec1ActualSparse) := by
  rcases
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_zfeat
      (Z := Bool) (r := 1) (k := 0) (m := 9)
      boolToBitVec1ActualSparse
      boolToBitVec1ActualSparse_injective
      (by decide)
      (by
        rw [card_exactVisiblePostSwitchSurface_bool0_actualSparse]
        norm_num [allAffinePointBlockFeatureCount_eq])
    with ⟨samples, hsamples⟩
  refine ⟨{ samples := samples, exact_family := ?_ }⟩
  calc
    (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily
        = fullExactVisibleRuleFamily Bool 0 := by
            simp [fullRuleActualSwitchedLocalInterface_predictorFamily]
    _ =
      sharedExactZABSparseThresholdAffineERMFamily
        (Z := Bool)
        (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
        (r := 1) (k := 0)
        (Index := ExactVisibleRule Bool 0)
        boolToBitVec1ActualSparse
        (allAffinePointBlockFeatures (1 + (0 + 0)))
        samples := by
            exact hsamples.symm

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_const_bool0_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface Bool 0)
          constBitVec1ActualSparse) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_eq_fullExactVisibleRuleFamily_of_not_injective_zfeat
      (T := fullRuleActualSwitchedLocalInterface Bool 0)
      constBitVec1ActualSparse
      (by simp [fullRuleActualSwitchedLocalInterface_predictorFamily])
      constBitVec1ActualSparse_not_injective

end Mettapedia.Computability.PNP
