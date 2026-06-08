import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdInjectiveERMLiveness

namespace Mettapedia.Computability.PNP

def boolToBitVec1 : Bool → BitVec 1 := fun b _ => b

theorem boolToBitVec1_injective : Function.Injective boolToBitVec1 := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

def exactVisiblePostSwitchSurfaceBool0Equiv :
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

theorem card_exactVisiblePostSwitchSurface_bool0 :
    Fintype.card (ExactVisiblePostSwitchSurface Bool 0) = 2 := by
  simpa using Fintype.card_congr exactVisiblePostSwitchSurfaceBool0Equiv

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_bool0_regression :
    ∃ samples :
        ExactVisibleRule Bool 0 → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool,
      sharedExactZABSparseThresholdAffineERMFamily
          (Z := Bool)
          (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
          (r := 1) (k := 0)
          (Index := ExactVisibleRule Bool 0)
          boolToBitVec1
          (allAffinePointBlockFeatures (1 + (0 + 0)))
          samples =
        fullExactVisibleRuleFamily Bool 0 := by
  refine
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_zfeat
      (Z := Bool) (r := 1) (k := 0) (m := 9)
      boolToBitVec1 boolToBitVec1_injective ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bool0]
    norm_num [allAffinePointBlockFeatureCount_eq]

end Mettapedia.Computability.PNP
