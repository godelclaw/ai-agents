import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction

/-!
# PNP crux: bit-coded fallback wrappers add no hidden compression

`ActualSwitchedLocalBoundedSampleMajorityObstruction` develops the exact
Hamming-cover geometry of bounded-sample plug-in majority with structured
fallback families.  This file extracts the smallest manuscript-facing wrapper
consequences into a compact interface:

- if the sample budget is zero, the wrapper contributes no expressivity beyond
  the fallback decoder itself;
- even with one sampled override, full-rule expressivity still pays an explicit
  additive bit budget.

These theorems are intended as route-level blockers that downstream synthesis
can cite without reopening the full fallback-cover development.
-/

namespace Mettapedia.Computability.PNP

universe v

namespace BitFallbackWrapper

/-- If the fallback decoder is already full-rule expressive, then the bounded
sample wrapper is automatically full-rule expressive as well.  The proof uses
the empty sample, so the sample budget itself contributes no extra power. -/
theorem surjective_of_fallback_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  have hwrapped :
      Function.Surjective
        (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down) := by
    intro rule
    rcases hsurj rule with ⟨code, hcode⟩
    exact ⟨ULift.up code, hcode⟩
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallback := fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
      hwrapped

/-- At zero sample radius, the wrapper has no hidden expressivity: it is
surjective exactly when the fallback decoder is surjective. -/
theorem zeroSample_surjective_iff_fallback_surjective
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

/-- Therefore a zero-sample bit-coded wrapper can only be full-rule expressive
once its fallback code budget reaches the exact-visible alphabet size. -/
theorem zeroSample_fallbackBits_ge_surfaceCard_of_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Strict reverse form of the previous theorem: below the exact-visible
truth-table budget, a zero-sample bit-coded wrapper cannot realize all rules. -/
theorem zeroSample_not_surjective_of_fallbackBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

/-- The zero-sample lower bound is sharp at the canonical truth-table decoder:
with one fallback bit per exact-visible input, the empty sample already leaves
the decoded rule unchanged. -/
theorem zeroSample_surjective_exactVisibleRuleDecode
    {Z : Type v} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    (Z := Z) (k := k)

/-- With one sampled override, full-rule expressivity still pays the exact
additive successor-count budget `fallbackBits + baseBits`, provided the
explicit one-sample support count `surfaceCard + 1` fits in `baseBits` bits. -/
theorem oneSample_fallbackBits_add_baseBits_ge_surfaceCard_of_surfaceCard_succ_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits + baseBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Strict reverse form for the exact one-sample successor-count budget. -/
theorem oneSample_not_surjective_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

/-- If a route states only the raw bound `surfaceCard ≤ 2 ^ baseBits`, the
one-sample successor count still costs one more bit. -/
theorem oneSample_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_surfaceCard_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Strict reverse form for the raw one-sample surface-cardinality bit bound. -/
theorem oneSample_not_surjective_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

end BitFallbackWrapper

end Mettapedia.Computability.PNP
