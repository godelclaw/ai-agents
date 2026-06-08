import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajoritySparseThresholdERMObstruction

/-!
# Regression checks for the sample-majority sparse-threshold ERM obstruction

These checks keep the unrestricted sample-level plug-in majority endpoint tied
to the later sparse-threshold ERM visible-budget obstructions.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def zeroExtractorBitVec2To0 : BitVec 2 → BitVec 0 := fun _ => zeroVec

/-- Positive-shape canary: if the unrestricted sample-majority endpoint on
`BitVec 2` were identified with one shared sparse-threshold ERM family at
extractor width `0`, Lean would already force the impossible inequality
`2 ≤ 1`. -/
theorem pluginSampleMajorityActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_visibleWidth_bound_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0)) :
    2 ≤ 1 := by
  simpa [zeroExtractorBitVec2To0] using
    pluginSampleMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 2) (k := 0) (r := 0)
      zeroExtractorBitVec2To0
      h

/-- Negative canary: the unrestricted sample-majority endpoint on `BitVec 2`
cannot be the manuscript-facing shared sparse-threshold ERM family at
extractor width `0`. -/
theorem pluginSampleMajorityActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_not_nonempty_sharedExactZABSparseThresholdERMData_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0) := by
  exact
    pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      zeroExtractorBitVec2To0
      (by norm_num)

/-- The stronger sparse-threshold recovery packet is likewise impossible on the
same unrestricted sample-majority endpoint at extractor width `0`. -/
theorem pluginSampleMajorityActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0
          q) := by
  exact
    pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      (μ := μ)
      zeroExtractorBitVec2To0
      q
      (by norm_num)

end Mettapedia.Computability.PNP
