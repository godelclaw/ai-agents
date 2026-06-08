import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveHeavyRegionCharacterization
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveRegionObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyActualSparseRecoverySurjectiveHeavyRegion :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨bitVec1ZeroVisiblePointActualSparseRecoveryRegion⟩

noncomputable local instance
    exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqActualSparseRecoverySurjectiveHeavyRegion :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

private theorem bitVec1SkewMeasureActualSparseRecoverySurjectiveHeavyRegion_apply_one :
    bitVec1SkewMeasureActualSparseRecoveryRegion
        bitVec1OneVisiblePointActualSparseRecoveryRegion =
      (1 : ℝ≥0∞) / 5 := by
  have honezero :
      bitVec1OneVisiblePointActualSparseRecoveryRegion ≠
        bitVec1ZeroVisiblePointActualSparseRecoveryRegion := by
    intro h
    exact bitVec1ZeroVisiblePointActualSparseRecoveryRegion_ne h.symm
  have hcount :
      bitVec1SkewSupportActualSparseRecoveryRegion.count
          bitVec1OneVisiblePointActualSparseRecoveryRegion =
        1 := by
    simp [bitVec1SkewSupportActualSparseRecoveryRegion, honezero]
  have hcard :
      Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion = 5 := by
    simp [bitVec1SkewSupportActualSparseRecoveryRegion]
  calc
    bitVec1SkewMeasureActualSparseRecoveryRegion
        bitVec1OneVisiblePointActualSparseRecoveryRegion
      =
        (bitVec1SkewSupportActualSparseRecoveryRegion.count
            bitVec1OneVisiblePointActualSparseRecoveryRegion : ℝ≥0∞) /
          Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion := by
            simp [bitVec1SkewMeasureActualSparseRecoveryRegion, PMF.ofMultiset_apply]
    _ = (1 : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion := by
      simpa using
        congrArg
          (fun n : ℕ =>
            (n : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion)
          hcount
    _ = (1 : ℝ≥0∞) / 5 := by
      simpa using congrArg (fun n : ℕ => (1 : ℝ≥0∞) / n) hcard

private theorem one_sub_one_fifth_eq_four_fifths_actualSparseRecoverySurjectiveHeavyRegion :
    (1 : ℝ≥0∞) - ((1 : ℝ≥0∞) / 5) = (4 : ℝ≥0∞) / 5 := by
  have hsum : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 5 + (1 : ℝ≥0∞) / 5 := by
    calc
      (1 : ℝ≥0∞) = (5 : ℝ≥0∞) / 5 := by
            exact (ENNReal.div_self (by norm_num) (by simp)).symm
      _ = ((4 : ℝ≥0∞) + 1) / 5 := by norm_num
      _ = (4 : ℝ≥0∞) / 5 + (1 : ℝ≥0∞) / 5 := by
            simpa using
              (ENNReal.div_add_div_same
                (a := (4 : ℝ≥0∞))
                (b := (1 : ℝ≥0∞))
                (c := (5 : ℝ≥0∞))).symm
  exact ENNReal.sub_eq_of_eq_add (by simp) hsum

private theorem three_quarters_lt_four_fifths_actualSparseRecoverySurjectiveHeavyRegion :
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

private theorem three_quarters_lt_lightestPoint_complement_actualSparseRecoverySurjectiveHeavyRegion :
    (3 : ℝ≥0∞) / 4 <
      1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
  have hlight :
      bitVec1SkewMeasureActualSparseRecoveryRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) ≤
        (1 : ℝ≥0∞) / 5 := by
    simpa [bitVec1SkewMeasureActualSparseRecoverySurjectiveHeavyRegion_apply_one] using
      (PMF.apply_lightestPoint_le_apply
        bitVec1SkewMeasureActualSparseRecoveryRegion
        bitVec1OneVisiblePointActualSparseRecoveryRegion)
  have hthreshold :
      (4 : ℝ≥0∞) / 5 ≤
        1 - bitVec1SkewMeasureActualSparseRecoveryRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
    have hsub :
        1 - ((1 : ℝ≥0∞) / 5) ≤
          1 - bitVec1SkewMeasureActualSparseRecoveryRegion
            (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) :=
      tsub_le_tsub_left hlight 1
    rwa [one_sub_one_fifth_eq_four_fifths_actualSparseRecoverySurjectiveHeavyRegion] at hsub
  exact
    lt_of_lt_of_le
      three_quarters_lt_four_fifths_actualSparseRecoverySurjectiveHeavyRegion
      hthreshold

/-- The theorem-shape canary on the duplicated-index surjective family: the
route already forces `q` above the lightest-point complement. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_surjectiveHeavyRegion_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) ≤ q := by
  rcases h with ⟨h⟩
  exact
    h.one_sub_apply_lightestPoint_le_of_surjective_predict
      (duplicatedFullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)

/-- Concrete threshold canary: on the same noninjective-surjective family, any
hypothetical recovery packet still forces `4/5 ≤ q`. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_surjectiveHeavyRegion_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  have hthreshold :
      (4 : ℝ≥0∞) / 5 ≤
        1 - bitVec1SkewMeasureActualSparseRecoveryRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
    have hlight :
        bitVec1SkewMeasureActualSparseRecoveryRegion
            (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) ≤
          (1 : ℝ≥0∞) / 5 := by
      simpa [bitVec1SkewMeasureActualSparseRecoverySurjectiveHeavyRegion_apply_one] using
        (PMF.apply_lightestPoint_le_apply
          bitVec1SkewMeasureActualSparseRecoveryRegion
          bitVec1OneVisiblePointActualSparseRecoveryRegion)
    have hsub :
        1 - ((1 : ℝ≥0∞) / 5) ≤
          1 - bitVec1SkewMeasureActualSparseRecoveryRegion
            (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) :=
      tsub_le_tsub_left hlight 1
    rwa [one_sub_one_fifth_eq_four_fifths_actualSparseRecoverySurjectiveHeavyRegion] at hsub
  exact le_trans
    hthreshold
    (duplicatedFullRuleActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_surjectiveHeavyRegion_regression
      h)

/-- Negative canary: the lightest-point threshold already rules out `q = 3/4`
on a surjective actual local family whose predictor map is not injective. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_surjectiveHeavyRegion_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (T := duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (duplicatedFullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      three_quarters_lt_lightestPoint_complement_actualSparseRecoverySurjectiveHeavyRegion

end Mettapedia.Computability.PNP
