import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryHeavyRegionCharacterization
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨zeroVec, zeroVec, zeroVec⟩

def bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨fun _ => true, zeroVec, zeroVec⟩

def idBitVec1ActualSparseRecoveryHeavyRegion : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k0NonemptyActualSparseRecoveryHeavyRegion :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ⟨bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion⟩

noncomputable def bitVec1BoundedSampleMajorityActualSparseRecoveryHeavyRegion :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 0 0

noncomputable local instance exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqActualSparseRecoveryHeavyRegion :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

theorem bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion_ne :
    bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion ≠
      bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion := by
  intro h
  have hz := congrArg (fun u => u.z) h
  have hbit := congrFun hz 0
  simp [bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion,
    bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion, zeroVec] at hbit

noncomputable def bitVec1SkewSupportActualSparseRecoveryHeavyRegion :
    Multiset (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ({bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion} : Multiset _) +
    {bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion} +
    {bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion} +
    {bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion} +
    {bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion}

noncomputable def bitVec1SkewMeasureActualSparseRecoveryHeavyRegion :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  PMF.ofMultiset bitVec1SkewSupportActualSparseRecoveryHeavyRegion (by
    simp [bitVec1SkewSupportActualSparseRecoveryHeavyRegion])

private theorem bitVec1SkewMeasureActualSparseRecoveryHeavyRegion_apply_one :
    bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
        bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion =
      (1 : ℝ≥0∞) / 5 := by
  have honezero :
      bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion ≠
        bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion := by
    intro h
    exact bitVec1ZeroVisiblePointActualSparseRecoveryHeavyRegion_ne h.symm
  have hcount :
      bitVec1SkewSupportActualSparseRecoveryHeavyRegion.count
          bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion =
        1 := by
    simp [bitVec1SkewSupportActualSparseRecoveryHeavyRegion, honezero]
  have hcard :
      Multiset.card bitVec1SkewSupportActualSparseRecoveryHeavyRegion = 5 := by
    simp [bitVec1SkewSupportActualSparseRecoveryHeavyRegion]
  calc
    bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
        bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion
      =
        (bitVec1SkewSupportActualSparseRecoveryHeavyRegion.count
            bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion : ℝ≥0∞) /
          Multiset.card bitVec1SkewSupportActualSparseRecoveryHeavyRegion := by
            simp [bitVec1SkewMeasureActualSparseRecoveryHeavyRegion, PMF.ofMultiset_apply]
    _ = (1 : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryHeavyRegion := by
      simpa using
        congrArg
          (fun n : ℕ =>
            (n : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryHeavyRegion)
          hcount
    _ = (1 : ℝ≥0∞) / 5 := by
      simpa using congrArg (fun n : ℕ => (1 : ℝ≥0∞) / n) hcard

private theorem one_sub_one_fifth_eq_four_fifths_actualSparseRecoveryHeavyRegion :
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

private theorem three_quarters_lt_four_fifths_actualSparseRecoveryHeavyRegion :
    (3 : ℝ≥0∞) / 4 < (4 : ℝ≥0∞) / 5 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 15 / 20 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  have h₂ : (4 : ℝ≥0∞) / 5 = 16 / 20 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem exists_heavyProperRegion_iff_exists_lt_one_sub_apply_bitVec1_skew_three_quarters_regression :
    (∃ region : Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0),
        (∃ x₀ : ExactVisiblePostSwitchSurface (BitVec 1) 0, x₀ ∉ region) ∧
          (3 : ℝ≥0∞) / 4 <
            region.sum (fun x => bitVec1SkewMeasureActualSparseRecoveryHeavyRegion x)) ↔
      ∃ y : ExactVisiblePostSwitchSurface (BitVec 1) 0,
        (3 : ℝ≥0∞) / 4 <
          1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion y := by
  exact
    ActualSwitchedLocalInterface.exists_heavyProperRegion_iff_exists_lt_one_sub_apply
      (μ := bitVec1SkewMeasureActualSparseRecoveryHeavyRegion)
      (k := 0)
      (q := (3 : ℝ≥0∞) / 4)

theorem exists_heavyProperRegion_iff_lt_one_sub_apply_lightestPoint_bitVec1_skew_three_quarters_regression :
    (∃ region : Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0),
        (∃ x₀ : ExactVisiblePostSwitchSurface (BitVec 1) 0, x₀ ∉ region) ∧
          (3 : ℝ≥0∞) / 4 <
            region.sum (fun x => bitVec1SkewMeasureActualSparseRecoveryHeavyRegion x)) ↔
      (3 : ℝ≥0∞) / 4 <
        1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) := by
  exact
    ActualSwitchedLocalInterface.exists_heavyProperRegion_iff_lt_one_sub_apply_lightestPoint
      (μ := bitVec1SkewMeasureActualSparseRecoveryHeavyRegion)
      (k := 0)
      (q := (3 : ℝ≥0∞) / 4)

theorem allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le_bitVec1_skew_three_quarters_regression :
    (∀ region : Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0),
        (∃ x₀ : ExactVisiblePostSwitchSurface (BitVec 1) 0, x₀ ∉ region) →
          region.sum (fun x => bitVec1SkewMeasureActualSparseRecoveryHeavyRegion x) ≤
            (3 : ℝ≥0∞) / 4) ↔
      1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) ≤
        (3 : ℝ≥0∞) / 4 := by
  exact
    ActualSwitchedLocalInterface.allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
      (μ := bitVec1SkewMeasureActualSparseRecoveryHeavyRegion)
      (k := 0)
      (q := (3 : ℝ≥0∞) / 4)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterfaceBitVec1k0SampleBound0_not_surjective_heavyRegion_regression :
    ¬ Function.Surjective
        bitVec1BoundedSampleMajorityActualSparseRecoveryHeavyRegion.predictorFamily.predict := by
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
      (Z := BitVec 1)
      (k := 0)
      (sampleBound := 0)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)

private theorem three_quarters_lt_lightestPoint_complement_actualSparseRecoveryHeavyRegion :
    (3 : ℝ≥0∞) / 4 <
      1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
        (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) := by
  have hlight :
      bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) ≤
        (1 : ℝ≥0∞) / 5 := by
    simpa [bitVec1SkewMeasureActualSparseRecoveryHeavyRegion_apply_one] using
      (PMF.apply_lightestPoint_le_apply
        bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
        bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion)
  have hthreshold :
      (4 : ℝ≥0∞) / 5 ≤
        1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) := by
    have hsub :
        1 - ((1 : ℝ≥0∞) / 5) ≤
          1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
            (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) :=
      tsub_le_tsub_left hlight 1
    rwa [one_sub_one_fifth_eq_four_fifths_actualSparseRecoveryHeavyRegion] at hsub
  exact
    lt_of_lt_of_le
      three_quarters_lt_four_fifths_actualSparseRecoveryHeavyRegion
      hthreshold

theorem not_allProperRegionMass_le_bitVec1_skew_three_quarters_regression :
    ¬ ∀ region : Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0),
        (∃ x₀ : ExactVisiblePostSwitchSurface (BitVec 1) 0, x₀ ∉ region) →
          region.sum (fun x => bitVec1SkewMeasureActualSparseRecoveryHeavyRegion x) ≤
            (3 : ℝ≥0∞) / 4 := by
  intro hregion
  have hbound :
      1 - bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          (PMF.lightestPoint bitVec1SkewMeasureActualSparseRecoveryHeavyRegion) ≤
        (3 : ℝ≥0∞) / 4 :=
    allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le_bitVec1_skew_three_quarters_regression.1
      hregion
  exact not_le_of_gt three_quarters_lt_lightestPoint_complement_actualSparseRecoveryHeavyRegion hbound

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_pointComplement_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          bitVec1BoundedSampleMajorityActualSparseRecoveryHeavyRegion
          idBitVec1ActualSparseRecoveryHeavyRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply
      (μ := bitVec1SkewMeasureActualSparseRecoveryHeavyRegion)
      (k := 0)
      (r := 1)
      (T := bitVec1BoundedSampleMajorityActualSparseRecoveryHeavyRegion)
      (zfeat := idBitVec1ActualSparseRecoveryHeavyRegion)
      (fun _ _ hxy => hxy)
      (by norm_num)
      (i := ⟨[], by simp⟩)
      (y := bitVec1OneVisiblePointActualSparseRecoveryHeavyRegion)
      (by
        rw [bitVec1SkewMeasureActualSparseRecoveryHeavyRegion_apply_one,
          one_sub_one_fifth_eq_four_fifths_actualSparseRecoveryHeavyRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoveryHeavyRegion)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_lightestPoint_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryHeavyRegion
          bitVec1BoundedSampleMajorityActualSparseRecoveryHeavyRegion
          idBitVec1ActualSparseRecoveryHeavyRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply_lightestPoint
      (μ := bitVec1SkewMeasureActualSparseRecoveryHeavyRegion)
      (k := 0)
      (r := 1)
      (sampleBound := 0)
      (zfeat := idBitVec1ActualSparseRecoveryHeavyRegion)
      (fun _ _ hxy => hxy)
      (by norm_num)
      three_quarters_lt_lightestPoint_complement_actualSparseRecoveryHeavyRegion

end Mettapedia.Computability.PNP
