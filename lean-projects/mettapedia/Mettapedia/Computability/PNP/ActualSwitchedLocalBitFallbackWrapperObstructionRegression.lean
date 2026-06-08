import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperObstruction

/-!
# Regression checks for bit-coded fallback wrapper obstructions

These wrappers keep the zero-sample and one-sample fallback consequences
available as small manuscript-facing entry points.
-/

namespace Mettapedia.Computability.PNP.BitFallbackWrapperObstructionRegression

open Mettapedia.Computability.PNP

example {Z : Type} {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  BitFallbackWrapper.surjective_of_fallback_surjective fallback hsurj

example {Z : Type} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  BitFallbackWrapper.zeroSample_surjective_iff_fallback_surjective fallback

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  BitFallbackWrapper.zeroSample_not_surjective_of_fallbackBits_lt_surfaceCard
    fallback hbits

example {Z : Type} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  BitFallbackWrapper.zeroSample_surjective_exactVisibleRuleDecode

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits + baseBits :=
  BitFallbackWrapper.oneSample_fallbackBits_add_baseBits_ge_surfaceCard_of_surfaceCard_succ_le_twoPow_surjective
    fallback hbase hsurj

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
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
  BitFallbackWrapper.oneSample_not_surjective_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    fallback hbase hbits

end Mettapedia.Computability.PNP.BitFallbackWrapperObstructionRegression
