import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginMajoritySparseThresholdERMRecoveryHeavyRegionCharacterization
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyActualSparseRecoveryPluginMajority :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨bitVec1ZeroVisiblePointActualSparseRecoveryRegion⟩

noncomputable local instance
    exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqActualSparseRecoveryPluginMajority :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

private theorem three_quarters_lt_four_fifths_actualSparseRecoveryPluginMajority :
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

private theorem four_fifths_le_lightestPoint_complement_actualSparseRecoveryPluginMajority :
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

private theorem three_quarters_lt_lightestPoint_complement_actualSparseRecoveryPluginMajority :
    (3 : ℝ≥0∞) / 4 <
      1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) := by
  exact
    lt_of_lt_of_le
      three_quarters_lt_four_fifths_actualSparseRecoveryPluginMajority
      four_fifths_le_lightestPoint_complement_actualSparseRecoveryPluginMajority

/-- The theorem-shape canary for unrestricted counted plug-in majority on the
skew `BitVec 1` witness: any hypothetical recovery packet already forces `q`
above the lightest-point complement. -/
theorem pluginMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (pluginMajorityActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    1 - bitVec1SkewMeasureActualSparseRecoveryRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryRegion) ≤ q := by
  simpa using
    pluginMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
      (Z := BitVec 1)
      (k := 0)
      (r := 1)
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (q := q)
      idBitVec1ActualSparseRecoveryRegion
      h

/-- Concrete threshold canary: on the same skew `BitVec 1` witness, any
hypothetical recovery packet on unrestricted counted plug-in majority still
forces `4/5 ≤ q`. -/
theorem pluginMajorityActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (pluginMajorityActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  exact le_trans
    four_fifths_le_lightestPoint_complement_actualSparseRecoveryPluginMajority
    (pluginMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_regression
      h)

/-- Negative canary: unrestricted counted plug-in majority on the skew
`BitVec 1` witness still cannot carry the recovery packet at `q = 3/4`. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (pluginMajorityActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    pluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
      (Z := BitVec 1)
      (k := 0)
      (r := 1)
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (q := (3 : ℝ≥0∞) / 4)
      idBitVec1ActualSparseRecoveryRegion
      three_quarters_lt_lightestPoint_complement_actualSparseRecoveryPluginMajority

end Mettapedia.Computability.PNP
