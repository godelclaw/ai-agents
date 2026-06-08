import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginLookupSparseThresholdERMObstruction

/-!
# Regression checks for the plug-in lookup sparse-threshold ERM obstruction

These checks keep the literal finite-alphabet lookup endpoint tied to the later
shared sparse-threshold ERM visible-budget obstruction.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def zeroExtractorBitVec2To0 : BitVec 2 → BitVec 0 := fun _ => zeroVec

/-- Positive-shape canary: if the unrestricted plug-in lookup endpoint on
`BitVec 2` were identified with one shared sparse-threshold ERM family at
extractor width `0`, Lean would already force the impossible inequality
`2 ≤ 1`. -/
theorem pluginLookupActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_visibleWidth_bound_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginLookupActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0)) :
    2 ≤ 1 := by
  simpa [zeroExtractorBitVec2To0] using
    pluginLookupActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := 2) (k := 0) (r := 0)
      zeroExtractorBitVec2To0
      h

/-- Negative canary: the unrestricted plug-in lookup endpoint on `BitVec 2`
cannot be the manuscript-facing shared sparse-threshold ERM family at
extractor width `0`. -/
theorem pluginLookupActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_not_nonempty_sharedExactZABSparseThresholdERMData_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginLookupActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0) := by
  exact
    pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      zeroExtractorBitVec2To0
      (by norm_num)

/-- The stronger sparse-threshold recovery packet is likewise impossible on the
same unrestricted plug-in lookup endpoint at extractor width `0`. -/
theorem pluginLookupActualSwitchedLocalInterfaceBitVec2k0_zeroExtractor_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginLookupActualSwitchedLocalInterface (BitVec 2) 0)
          zeroExtractorBitVec2To0
          q) := by
  exact
    pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      (μ := μ)
      zeroExtractorBitVec2To0
      q
      (by norm_num)

end Mettapedia.Computability.PNP
