import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveHeavyRegionCharacterization

/-!
# PNP crux: a surjective fallback side channel does not escape the
  lightest-point recovery threshold

`ActualSwitchedLocalBitFallbackWrapperObstruction` isolates the route where a
bounded-sample plug-in-majority endpoint is wrapped around a bit-coded fallback
decoder.  If that decoder is already surjective onto all exact-visible Boolean
rules, then the empty sample leaves the fallback rule unchanged, so the wrapped
endpoint remains surjective for every sample budget.

This file transfers the sharper `q`-dependent recovery obstruction to that
repair path.  Once the wrapped endpoint is still surjective on the full
exact-visible rule family, the recent surjective heavy-region characterization
already forces

* `1 - μ (PMF.lightestPoint μ) ≤ q`.

So "majority plus a full-rule fallback decoder" does not avoid the later
recovery threshold either; it is still just another surjective actual-local
endpoint.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}

/-- If the fallback decoder is already surjective, then any hypothetical
sparse-threshold recovery packet on the wrapped endpoint forces `q` above the
lightest-point complement mass. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  rcases h with ⟨h⟩
  exact
    h.one_sub_apply_lightestPoint_le_of_surjective_predict
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj)

/-- Therefore a surjective fallback decoder cannot rescue the wrapped endpoint
below the lightest-point threshold. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback)
      (zfeat := zfeat)
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj)
      hq_lt

/-- In particular, the canonical truth-table fallback decoder cannot rescue
the wrapped endpoint below the same lightest-point threshold. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k)))
      (zfeat := zfeat)
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))
      hq_lt

end Abstract

end Mettapedia.Computability.PNP
