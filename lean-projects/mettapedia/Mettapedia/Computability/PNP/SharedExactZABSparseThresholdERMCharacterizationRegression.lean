import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdERMCharacterization

namespace Mettapedia.Computability.PNP

def boolToBitVec1Char : Bool → BitVec 1 := fun b _ => b

theorem boolToBitVec1Char_injective : Function.Injective boolToBitVec1Char := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

def constBitVec1Char : Bool → BitVec 1 := fun _ _ => false

theorem constBitVec1Char_not_injective : ¬ Function.Injective constBitVec1Char := by
  intro hinj
  have h : false = true := hinj (a₁ := false) (a₂ := true) rfl
  exact Bool.false_ne_true h

def exactVisiblePostSwitchSurfaceBool0EquivChar :
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

theorem card_exactVisiblePostSwitchSurface_bool0_char :
    Fintype.card (ExactVisiblePostSwitchSurface Bool 0) = 2 := by
  simpa using Fintype.card_congr exactVisiblePostSwitchSurfaceBool0EquivChar

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_zfeat_bool0_regression :
    (∃ samples :
        ExactVisibleRule Bool 0 → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool,
      sharedExactZABSparseThresholdAffineERMFamily
          (Z := Bool)
          (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
          (r := 1) (k := 0)
          (Index := ExactVisibleRule Bool 0)
          boolToBitVec1Char
          (allAffinePointBlockFeatures (1 + (0 + 0)))
          samples =
        fullExactVisibleRuleFamily Bool 0) ↔
      Function.Injective boolToBitVec1Char := by
  refine
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_zfeat
      (Z := Bool) (r := 1) (k := 0) (m := 9) boolToBitVec1Char ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bool0_char]
    norm_num [allAffinePointBlockFeatureCount_eq]

theorem not_exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_const_bool0_regression :
    ¬ ∃ samples :
        ExactVisibleRule Bool 0 → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool,
      sharedExactZABSparseThresholdAffineERMFamily
          (Z := Bool)
          (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
          (r := 1) (k := 0)
          (Index := ExactVisibleRule Bool 0)
          constBitVec1Char
          (allAffinePointBlockFeatures (1 + (0 + 0)))
          samples =
        fullExactVisibleRuleFamily Bool 0 := by
  intro hEq
  exact
    constBitVec1Char_not_injective
      ((exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_zfeat
        (Z := Bool) (r := 1) (k := 0) (m := 9) constBitVec1Char
        (by decide)
        (by
          rw [card_exactVisiblePostSwitchSurface_bool0_char]
          norm_num [allAffinePointBlockFeatureCount_eq])).1 hEq)

end Mettapedia.Computability.PNP
