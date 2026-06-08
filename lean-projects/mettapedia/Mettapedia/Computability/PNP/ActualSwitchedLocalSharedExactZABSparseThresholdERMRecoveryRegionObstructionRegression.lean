import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def bitVec1ZeroVisiblePointActualSparseRecoveryRegion :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨zeroVec, zeroVec, zeroVec⟩

def bitVec1OneVisiblePointActualSparseRecoveryRegion :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨fun _ => true, zeroVec, zeroVec⟩

def idBitVec1ActualSparseRecoveryRegion : BitVec 1 → BitVec 1 := fun x => x

noncomputable local instance exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqActualSparseRecoveryRegion :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

theorem bitVec1ZeroVisiblePointActualSparseRecoveryRegion_ne :
    bitVec1ZeroVisiblePointActualSparseRecoveryRegion ≠
      bitVec1OneVisiblePointActualSparseRecoveryRegion := by
  intro h
  have hz := congrArg (fun u => u.z) h
  have hbit := congrFun hz 0
  simp [bitVec1ZeroVisiblePointActualSparseRecoveryRegion,
    bitVec1OneVisiblePointActualSparseRecoveryRegion, zeroVec] at hbit

noncomputable def bitVec1SkewSupportActualSparseRecoveryRegion :
    Multiset (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  ({bitVec1ZeroVisiblePointActualSparseRecoveryRegion} : Multiset _) +
    {bitVec1ZeroVisiblePointActualSparseRecoveryRegion} +
    {bitVec1ZeroVisiblePointActualSparseRecoveryRegion} +
    {bitVec1ZeroVisiblePointActualSparseRecoveryRegion} +
    {bitVec1OneVisiblePointActualSparseRecoveryRegion}

noncomputable def bitVec1SkewMeasureActualSparseRecoveryRegion :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  PMF.ofMultiset bitVec1SkewSupportActualSparseRecoveryRegion (by
    simp [bitVec1SkewSupportActualSparseRecoveryRegion])

def bitVec1HeavyRegionActualSparseRecoveryRegion :
    Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  {bitVec1ZeroVisiblePointActualSparseRecoveryRegion}

theorem bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion :
    bitVec1OneVisiblePointActualSparseRecoveryRegion ∉
      bitVec1HeavyRegionActualSparseRecoveryRegion := by
  simpa [bitVec1HeavyRegionActualSparseRecoveryRegion] using
    bitVec1ZeroVisiblePointActualSparseRecoveryRegion_ne.symm

theorem bitVec1HeavyRegion_massActualSparseRecoveryRegion :
    bitVec1HeavyRegionActualSparseRecoveryRegion.sum
        (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x) =
      (4 : ℝ≥0∞) / 5 := by
  have hcount :
      bitVec1SkewSupportActualSparseRecoveryRegion.count
          bitVec1ZeroVisiblePointActualSparseRecoveryRegion =
        4 := by
    simp [bitVec1SkewSupportActualSparseRecoveryRegion,
      bitVec1ZeroVisiblePointActualSparseRecoveryRegion_ne]
  have hcard : Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion = 5 := by
    simp [bitVec1SkewSupportActualSparseRecoveryRegion]
  calc
    bitVec1HeavyRegionActualSparseRecoveryRegion.sum
        (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x)
      = bitVec1SkewMeasureActualSparseRecoveryRegion
          bitVec1ZeroVisiblePointActualSparseRecoveryRegion := by
            simp [bitVec1HeavyRegionActualSparseRecoveryRegion]
    _ =
        (bitVec1SkewSupportActualSparseRecoveryRegion.count
            bitVec1ZeroVisiblePointActualSparseRecoveryRegion : ℝ≥0∞) /
          Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion := by
            simp [bitVec1SkewMeasureActualSparseRecoveryRegion, PMF.ofMultiset_apply]
    _ = (4 : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion := by
      simpa using
        congrArg
          (fun n : ℕ =>
            (n : ℝ≥0∞) / Multiset.card bitVec1SkewSupportActualSparseRecoveryRegion)
          hcount
    _ = (4 : ℝ≥0∞) / 5 := by
      simpa using congrArg (fun n : ℕ => (4 : ℝ≥0∞) / n) hcard

private theorem three_quarters_lt_four_fifths_actualSparseRecoveryRegion :
    (3 : ℝ≥0∞) / 4 < (4 : ℝ≥0∞) / 5 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 15 / 20 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  have h₂ : (4 : ℝ≥0∞) / 5 = 16 / 20 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_four_fifths_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          q)) :
    (4 : ℝ≥0∞) / 5 ≤ q := by
  by_contra hq
  have hmass :
      q <
        bitVec1HeavyRegionActualSparseRecoveryRegion.sum
          (fun x => bitVec1SkewMeasureActualSparseRecoveryRegion x) := by
    rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
    exact lt_of_not_ge hq
  exact
    (ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (k := 0)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (fun _ _ hxy => hxy)
      (by norm_num)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      ⟨bitVec1OneVisiblePointActualSparseRecoveryRegion,
        bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion⟩
      hmass) h

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (k := 0)
      (r := 1)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (fun _ _ hxy => hxy)
      (by norm_num)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      ⟨bitVec1OneVisiblePointActualSparseRecoveryRegion,
        bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion⟩
      (by
        rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoveryRegion)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_skew_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1SkewMeasureActualSparseRecoveryRegion
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 0 2)
          idBitVec1ActualSparseRecoveryRegion
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
      (μ := bitVec1SkewMeasureActualSparseRecoveryRegion)
      (k := 0)
      (r := 1)
      (sampleBound := 2)
      (zfeat := idBitVec1ActualSparseRecoveryRegion)
      (fun _ _ hxy => hxy)
      (by norm_num)
      bitVec1HeavyRegionActualSparseRecoveryRegion
      ⟨bitVec1OneVisiblePointActualSparseRecoveryRegion,
        bitVec1OneVisiblePointActualSparseRecoveryRegion_not_mem_heavyRegion⟩
      (by
        rw [bitVec1HeavyRegion_massActualSparseRecoveryRegion]
        exact three_quarters_lt_four_fifths_actualSparseRecoveryRegion)

end Mettapedia.Computability.PNP
