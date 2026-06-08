import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMWidthCharacterization
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

theorem exists_injective_bitVecExtractor_iff_width_le_1_1_regression :
    (∃ zfeat : BitVec 1 → BitVec 1, Function.Injective zfeat) ↔ 1 ≤ 1 := by
  exact
    ActualSwitchedLocalInterface.exists_injective_bitVecExtractor_iff_width_le
      (n := 1) (r := 1)

theorem exists_injective_bitVecExtractor_iff_width_le_1_0_regression :
    (∃ zfeat : BitVec 1 → BitVec 0, Function.Injective zfeat) ↔ 1 ≤ 0 := by
  exact
    ActualSwitchedLocalInterface.exists_injective_bitVecExtractor_iff_width_le
      (n := 1) (r := 0)

theorem fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le_1_1_regression :
    (∃ zfeat : BitVec 1 → BitVec 1,
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          zfeat)) ↔
      1 ≤ 1 := by
  refine
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le
      (n := 1) (r := 1) (k := 0) (m := 17) ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bitVec]
    norm_num [allAffinePointBlockFeatureCount_eq]

theorem fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le_1_0_k1_regression :
    (∃ zfeat : BitVec 1 → BitVec 0,
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          zfeat)) ↔
      1 ≤ 0 := by
  refine
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le
      (n := 1) (r := 0) (k := 1) (m := 200) ?_ ?_
  · decide
  · rw [card_exactVisiblePostSwitchSurface_bitVec]
    norm_num [allAffinePointBlockFeatureCount_eq]

theorem fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_1_1_regression :
    ∃ zfeat : BitVec 1 → BitVec 1,
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          zfeat) := by
  exact
    fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le_1_1_regression.2
      (by decide)

theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMData_1_0_k1_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
            zfeat) := by
  intro h
  have hle :
      1 ≤ 0 :=
    fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le_1_0_k1_regression.1 h
  exact Nat.not_succ_le_zero 0 hle

end Mettapedia.Computability.PNP
