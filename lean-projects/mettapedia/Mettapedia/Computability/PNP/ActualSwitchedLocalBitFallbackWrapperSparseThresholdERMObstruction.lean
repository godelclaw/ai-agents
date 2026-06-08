import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryVisibleBudgetObstruction

/-!
# PNP crux: a surjective fallback side channel does not repair the
  sparse-threshold ERM route

`ActualSwitchedLocalBitFallbackWrapperObstruction` isolates the manuscript-side
repair path where bounded sampled overrides are wrapped around a bit-coded
fallback decoder.  If that fallback decoder is already surjective onto all
exact-visible Boolean rules, then the wrapped endpoint is surjective for every
sample budget: the empty sample simply leaves the fallback rule unchanged.

This file packages the corresponding route-level consequence.  Once the wrapped
endpoint is still surjective on the full exact-visible rule family, the same
shared sparse-threshold ERM visible-budget obstruction applies immediately.
So "majority plus a full-rule fallback side channel" is not a repair to the
existing sparse-threshold ERM obstruction; it is just another surjective
actual-local endpoint.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}

/-- If a bit-coded fallback decoder is already full-rule expressive, then the
bounded-sample majority wrapper cannot carry shared exact sparse-threshold ERM
data below the point-block visible-budget threshold. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback)
      zfeat
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj)
      hs

/-- The same surjective fallback side channel also cannot carry the stronger
manuscript-facing sparse-threshold recovery packet below the same visible-budget
threshold. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_lt_surfaceCard
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hs <|
    h.surfaceCard_le_of_surjective_predict
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj)

end Abstract

section BitVec

variable {n k r sampleBound fallbackBits : ℕ}

/-- On `BitVec n`, a bounded-sample majority wrapper with a surjective
bit-coded fallback decoder inherits the same unconditional half-width ceiling as
any other surjective endpoint carrying shared exact sparse-threshold ERM data.
-/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := BitVec n) (k := k) (sampleBound := sampleBound) fallback hsurj)

/-- Therefore a surjective fallback side channel does not rescue the wrapped
endpoint below the unconditional sparse-threshold visible-budget width bound. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        (BitVec n) k sampleBound fallbackBits fallback)
      zfeat
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := BitVec n) (k := k) (sampleBound := sampleBound) fallback hsurj)
      hgap

/-- The stronger sparse-threshold recovery packet inherits the same
unconditional half-width ceiling on a bounded-sample majority wrapper whose
fallback decoder is already surjective. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := BitVec n) (k := k) (sampleBound := sampleBound) fallback hsurj)

/-- Hence the wrapped endpoint also cannot carry the stronger recovery packet
below the same unconditional sparse-threshold visible-budget width bound. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        (BitVec n) k sampleBound fallbackBits fallback)
      (μ := μ)
      (zfeat := zfeat)
      (q := q)
      (BitFallbackWrapper.surjective_of_fallback_surjective
        (Z := BitVec n) (k := k) (sampleBound := sampleBound) fallback hsurj)
      hgap

end BitVec

end Mettapedia.Computability.PNP
