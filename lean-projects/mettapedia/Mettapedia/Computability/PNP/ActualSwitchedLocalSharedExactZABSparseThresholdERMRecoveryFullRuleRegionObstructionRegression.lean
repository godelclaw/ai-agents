import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryFullRuleRegionObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstructionRegression
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

theorem bitVec1HeavyRegionActualSparseRecoveryFullRuleRegion_card :
    bitVec1HeavyRegionActualSparseRecoveryRegion.card = 1 := by
  simp [bitVec1HeavyRegionActualSparseRecoveryRegion]

theorem bitVec1HeavyRegionActualSparseRecoveryFullRuleRegion_card_lt_surfaceCard :
    bitVec1HeavyRegionActualSparseRecoveryRegion.card <
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 0) := by
  rw [bitVec1HeavyRegionActualSparseRecoveryFullRuleRegion_card]
  rw [card_exactVisiblePostSwitchSurface_bitVec]
  norm_num

private theorem three_quarters_lt_four_fifths_actualSparseRecoveryFullRuleRegion :
    (3 : ℝ≥0∞) / 4 < (4 : ℝ≥0∞) / 5 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 15 / 20 := by
    refine
      (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  have h₂ : (4 : ℝ≥0∞) / 5 = 16 / 20 := by
    refine
      (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

/-- The theorem-shape canary: on the skew `BitVec 1` measure, any hypothetical
full-rule recovery packet already forces the heavy singleton region mass
`4/5` to lie below `q`, with no appeal to the old injective-branch theorem. -/
theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_fullRuleRegion_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  rcases h with ⟨h⟩
  have hmass :
      bitVec1HeavyRegionActualSparseRecoveryRegion.sum
          (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x) ≤
        q :=
    h.regionMass_le_of_lt_surfaceCard
      bitVec1HeavyRegionActualSparseRecoveryRegion
      bitVec1HeavyRegionActualSparseRecoveryFullRuleRegion_card_lt_surfaceCard
  simpa [bitVec1HeavyRegion_massActualSparseRecoveryRegion] using hmass

/-- Negative canary: on the same skew `BitVec 1` measure, the full-rule
recovery endpoint is impossible already at `q = 3/4` by the new full-rule
proper-region obstruction, without using the old injective-branch hypothesis. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_fullRuleRegion_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (k := 0)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      bitVec1HeavyRegionActualSparseRecoveryFullRuleRegion_card_lt_surfaceCard
      (by
        rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoveryFullRuleRegion)

end Mettapedia.Computability.PNP
