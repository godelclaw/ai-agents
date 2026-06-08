import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMObstruction

/-!
# Regression checks for the fallback-wrapper sparse-threshold ERM obstruction

These checks keep the "majority plus fallback side channel" repair path tied to
the same sparse-threshold ERM visible-budget obstruction.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def zeroExtractorBitVec2To0BitFallbackSparseThreshold : BitVec 2 → BitVec 0 := fun _ => zeroVec

theorem exactVisibleRuleDecode_surjective_bitVec2k0 :
    Function.Surjective
      (exactVisibleRuleDecode (Z := BitVec 2) (k := 0)) := by
  intro rule
  refine ⟨exactVisibleRuleEncode (Z := BitVec 2) (k := 0) rule, ?_⟩
  simpa using exactVisibleRuleDecode_encode (Z := BitVec 2) (k := 0) rule

/-- Positive-shape canary: even adding a surjective fallback decoder and one
sampled override to plug-in majority would force the impossible inequality
`2 ≤ 1` if this wrapped endpoint were identified with one shared exact
sparse-threshold ERM family at extractor width `0`. -/
theorem bitFallbackWrapperBitVec2k0_oneSample_exactVisibleRuleDecode_visibleWidth_bound_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec 2) 0 1
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
            (exactVisibleRuleDecode (Z := BitVec 2) (k := 0)))
          zeroExtractorBitVec2To0BitFallbackSparseThreshold)) :
    2 ≤ 1 := by
  simpa [zeroExtractorBitVec2To0BitFallbackSparseThreshold] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective
      (n := 2) (k := 0) (r := 0) (sampleBound := 1)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
      (fallback := exactVisibleRuleDecode (Z := BitVec 2) (k := 0))
      exactVisibleRuleDecode_surjective_bitVec2k0
      zeroExtractorBitVec2To0BitFallbackSparseThreshold
      h

/-- Negative canary: the one-sample bit-fallback wrapper with the canonical
truth-table fallback decoder cannot be the manuscript-facing shared exact
sparse-threshold ERM family at extractor width `0`. -/
theorem bitFallbackWrapperBitVec2k0_oneSample_exactVisibleRuleDecode_not_nonempty_sharedExactZABSparseThresholdERMData_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec 2) 0 1
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
            (exactVisibleRuleDecode (Z := BitVec 2) (k := 0)))
          zeroExtractorBitVec2To0BitFallbackSparseThreshold) := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0) (sampleBound := 1)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
      (fallback := exactVisibleRuleDecode (Z := BitVec 2) (k := 0))
      exactVisibleRuleDecode_surjective_bitVec2k0
      zeroExtractorBitVec2To0BitFallbackSparseThreshold
      (by norm_num)

/-- The stronger sparse-threshold recovery packet is likewise impossible on the
same one-sample fallback-wrapped endpoint at extractor width `0`. -/
theorem bitFallbackWrapperBitVec2k0_oneSample_exactVisibleRuleDecode_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec 2) 0 1
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
            (exactVisibleRuleDecode (Z := BitVec 2) (k := 0)))
          zeroExtractorBitVec2To0BitFallbackSparseThreshold
          q) := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0) (sampleBound := 1)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec 2) 0))
      (fallback := exactVisibleRuleDecode (Z := BitVec 2) (k := 0))
      exactVisibleRuleDecode_surjective_bitVec2k0
      (μ := μ)
      zeroExtractorBitVec2To0BitFallbackSparseThreshold
      q
      (by norm_num)

end Mettapedia.Computability.PNP
