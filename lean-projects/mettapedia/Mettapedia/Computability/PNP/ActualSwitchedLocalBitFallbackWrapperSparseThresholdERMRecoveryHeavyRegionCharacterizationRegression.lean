import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMRecoveryHeavyRegionCharacterization
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyActualSparseRecoveryBitFallback :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨bitVec1ZeroVisiblePointActualSparseRecoveryRegion⟩

noncomputable local instance
    exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqActualSparseRecoveryBitFallback :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

noncomputable def oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface :
    ActualSwitchedLocalInterface
      (BitVec 1) 0
      (BoundedSampleFallbackFamilyIndex
        (ULift.{0} (BitCode (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 0))))
        (ExactVisiblePostSwitchSurface (BitVec 1) 0)
        1)
      (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
    (BitVec 1) 0 1
    (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 0))
    (exactVisibleRuleDecode (Z := BitVec 1) (k := 0))

private theorem three_quarters_lt_four_fifths_actualSparseRecoveryBitFallback :
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

private theorem four_fifths_le_lightestPoint_complement_actualSparseRecoveryBitFallback :
    (4 : ℝ≥0∞) / 5 ≤
      1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
  have hregion :
      bitVec1HeavyRegionActualSparseRecoveryRegion.sum
          (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x) ≤
        1 - bitVec1SkewMeasureActualSparseRecoveryRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) :=
    PMF.sum_le_one_sub_apply_lightestPoint_of_exists_not_mem
      bitVec1SkewMeasureActualSparseRecoveryRegion
      ⟨bitVec1OneVisiblePointActualSparseRecoveryRegion,
        bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion⟩
  simpa [bitVec1HeavyRegion_massActualSparseRecoveryRegion] using hregion

private theorem three_quarters_lt_lightestPoint_complement_actualSparseRecoveryBitFallback :
    (3 : ℝ≥0∞) / 4 <
      1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
  exact
    lt_of_lt_of_le
      three_quarters_lt_four_fifths_actualSparseRecoveryBitFallback
      four_fifths_le_lightestPoint_complement_actualSparseRecoveryBitFallback

/-- The theorem-shape canary for the one-sample wrapped endpoint with the
canonical truth-table fallback decoder: any hypothetical recovery packet
already forces `q` above the lightest-point complement. -/
theorem oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) ≤ q := by
  have hsurj :
      Function.Surjective
        (exactVisibleRuleDecode (Z := BitVec 1) (k := 0)) := by
    intro rule
    refine ⟨exactVisibleRuleEncode (Z := BitVec 1) (k := 0) rule, ?_⟩
    simpa using exactVisibleRuleDecode_encode (Z := BitVec 1) (k := 0) rule
  simpa [oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
      (Z := BitVec 1)
      (k := 0)
      (r := 1)
      (sampleBound := 1)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 0))
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (q := q)
      (fallback := exactVisibleRuleDecode (Z := BitVec 1) (k := 0))
      hsurj
      idBitVec1ActualSparseRecoveryRegion
      h

/-- Concrete threshold canary: on the same skew `BitVec 1` witness, any
hypothetical recovery packet on the wrapped endpoint still forces `4/5 ≤ q`. -/
theorem oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  exact le_trans
    four_fifths_le_lightestPoint_complement_actualSparseRecoveryBitFallback
    (oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_regression
      h)

/-- Negative canary: even after adding one sampled override on top of the
canonical full-rule fallback decoder, the skew `BitVec 1` witness still rules
out `q = 3/4`. -/
theorem oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  simpa [oneSampleExactVisibleRuleDecodeActualSwitchedLocalInterface] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
      (Z := BitVec 1)
      (k := 0)
      (r := 1)
      (sampleBound := 1)
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (q := (3 : ℝ≥0∞) / 4)
      three_quarters_lt_lightestPoint_complement_actualSparseRecoveryBitFallback

end Mettapedia.Computability.PNP
