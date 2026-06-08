import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackZeroSampleImage

/-!
# Regression checks for zero-sample bit fallback image equivalence

These wrappers keep the stronger radius-zero predictor-image equivalence
available as a small route-facing interface.
-/

namespace Mettapedia.Computability.PNP.BitFallbackZeroSampleImageRegression

open Mettapedia.Computability.PNP

example {Z : Type} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index : BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits,
        (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).predict index = rule) ↔
      ∃ code : BitCode fallbackBits, fallback code = rule :=
  BitFallbackZeroSampleImage.realizes_rule_iff_exists_fallbackCode fallback rule

example {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorCover N :=
  BitFallbackZeroSampleImage.finitePredictorCover_iff_fallbackDecoderFamily fallback

example {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N :=
  BitFallbackZeroSampleImage.finiteIndexRepresentativeCover_iff_fallbackDecoderFamily fallback

example {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorQuotient N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorQuotient N :=
  BitFallbackZeroSampleImage.finitePredictorQuotient_iff_fallbackDecoderFamily fallback

example {Z : Type} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
        (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback) s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitCode fallbackBits)
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s :=
  BitFallbackZeroSampleImage.exactVisibleCompressionTarget_iff_fallbackDecoderFamily
    fallback

example {Z : Type} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).RealizedByClockedBitFamily F :=
  BitFallbackZeroSampleImage.exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
    fallback

end Mettapedia.Computability.PNP.BitFallbackZeroSampleImageRegression
