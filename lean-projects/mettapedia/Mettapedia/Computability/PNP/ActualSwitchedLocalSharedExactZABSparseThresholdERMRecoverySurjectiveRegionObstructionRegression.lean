import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveRegionObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

/-- A deliberately duplicated-index full-rule local interface: it is still
surjective onto all exact visible Boolean rules, but its actual index map is not
injective because the first Boolean coordinate is ignored. -/
def duplicatedFullRuleActualSwitchedLocalInterface
    (Z : Type*) (k : ℕ) :
    ActualSwitchedLocalInterface
      Z k (Bool × ExactVisibleRule Z k) (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun idx u => idx.2 u
  output := fun idx u => idx.2 u
  output_eq_local := by
    intro idx u
    rfl

theorem duplicatedFullRuleActualSwitchedLocalInterface_surjective
    (Z : Type*) (k : ℕ) :
    Function.Surjective
      (duplicatedFullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  intro rule
  exact ⟨(false, rule), rfl⟩

theorem duplicatedFullRuleActualSwitchedLocalInterface_not_injective_predict
    (Z : Type*) (k : ℕ) :
    ¬ Function.Injective
        (duplicatedFullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  intro hinj
  let rule : ExactVisibleRule Z k := fun _ => false
  have hEq :
      (duplicatedFullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict (false, rule) =
        (duplicatedFullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict
          (true, rule) := by
    rfl
  have hPair := hinj hEq
  have hfst : false = true := congrArg Prod.fst hPair
  simp at hfst

private theorem three_quarters_lt_four_fifths_actualSparseRecoverySurjectiveRegion :
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

/-- The theorem-shape canary: even for a surjective actual local family whose
predictor map is not injective, any hypothetical recovery packet already forces
the heavy-region mass `4/5` below `q`. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_surjectiveRegion_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  rcases h with ⟨h⟩
  have hmass :
      bitVec1HeavyRegionActualSparseRecoveryRegion.sum
          (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x) ≤ q :=
    h.regionMass_le_of_surjective_predict_of_not_mem
      (duplicatedFullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion
  simpa [bitVec1HeavyRegion_massActualSparseRecoveryRegion] using hmass

/-- Negative canary: the same skew `BitVec 1` measure blocks recovery at
`q = 3/4` on a surjective actual local family whose predictor map is not
injective, so the new theorem is not merely another injective-family wrapper. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_surjectiveRegion_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_mem_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (T := duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (duplicatedFullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion
      (by
        rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoverySurjectiveRegion)

/-- The same duplicated-index surjective family cannot be rescued by changing
the extractor: once the heavy region already has mass above `q`, no
`BitVec 1 → BitVec 1` extractor can support the manuscript-facing recovery
packet. -/
theorem duplicatedFullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_surjectiveRegion_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1SkewMeasureActualSparseRecoveryRegion
            (duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
            zfeat
            ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_mem_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (T := duplicatedFullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (r := 1)
      (q := (3 : ℝ≥0∞) / 4)
      (duplicatedFullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion
      (by
        rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoverySurjectiveRegion)

end Mettapedia.Computability.PNP
