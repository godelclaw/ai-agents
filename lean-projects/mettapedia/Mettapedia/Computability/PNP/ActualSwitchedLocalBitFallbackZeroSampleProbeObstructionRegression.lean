import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackZeroSampleProbeObstruction

/-!
# Regression checks for zero-sample bit fallback probe obstructions

These wrappers keep the injective finite-probe lower bounds available as a
small route-facing interface.
-/

namespace Mettapedia.Computability.PNP.BitFallbackZeroSampleProbeObstructionRegression

open Mettapedia.Computability.PNP

example {Probe : Type} [Fintype Probe]
    {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hcover :
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  BitFallbackZeroSampleProbeObstruction.finitePredictorCover_card_le_of_fallback_injective_realization
    fallback target hinj hreal hcover

example {Probe : Type} [Fintype Probe]
    {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hrep :
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  BitFallbackZeroSampleProbeObstruction.finiteIndexRepresentativeCover_card_le_of_fallback_injective_realization
    fallback target hinj hreal hrep

example {Probe : Type} [Fintype Probe]
    {Z : Type} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hN : N < Fintype.card Probe) :
    ¬ (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorQuotient N :=
  BitFallbackZeroSampleProbeObstruction.not_finitePredictorQuotient_of_fallback_injective_realization_of_lt_card
    fallback target hinj hreal hN

example {Probe : Type} [Fintype Probe]
    {Z : Type} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget
      (Z := Z) (k := k)
      (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback) s :=
  BitFallbackZeroSampleProbeObstruction.not_exactVisibleCompressionTarget_of_fallback_injective_realization_of_lt_card
    fallback target hinj hreal hs

example {Probe : Type} [Fintype Probe]
    {Z : Type} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).RealizedByClockedBitFamily F :=
  BitFallbackZeroSampleProbeObstruction.not_exists_clockedExactVisibleRealization_of_fallback_injective_realization_of_lt_card
    fallback target hinj hreal hs

end Mettapedia.Computability.PNP.BitFallbackZeroSampleProbeObstructionRegression
