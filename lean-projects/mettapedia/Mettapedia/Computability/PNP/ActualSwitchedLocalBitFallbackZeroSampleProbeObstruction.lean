import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackZeroSampleImage

/-!
# PNP crux: zero-sample bit fallback wrappers inherit every fallback probe lower bound

`ActualSwitchedLocalBitFallbackZeroSampleImage` proves that a radius-zero
bit-coded fallback wrapper has exactly the same predictor image as the raw
fallback decoder family.  This file packages the first robust consequence:
every injectively realized finite probe family already contained in the
fallback decoder image survives unchanged through the radius-zero wrapper.

Therefore any such probe lower bound blocks:

- finite predictor-image covers;
- finite representative-index covers;
- finite quotient-code presentations;
- exact visible compression targets;
- clocked exact-visible realizations.

At sample radius zero the wrapper cannot compress away even a partially large
fallback image.
-/

namespace Mettapedia.Computability.PNP

universe v

namespace BitFallbackZeroSampleProbeObstruction

/-- If the raw fallback decoder family already realizes an injectively indexed
finite probe family, then any finite predictor-image cover of the radius-zero
wrapper must contain at least that many predictors. -/
theorem finitePredictorCover_card_le_of_fallback_injective_realization
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hcover :
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  have hcoverFallback :
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorCover N :=
    (BitFallbackZeroSampleImage.finitePredictorCover_iff_fallbackDecoderFamily
      fallback).mp hcover
  exact
    exactVisible_finitePredictorCover_card_le_of_injective_realization
      (G := BitFallbackZeroSampleImage.fallbackDecoderFamily fallback)
      target hinj
      (by
        intro p
        rcases hreal p with ⟨code, hcode⟩
        exact ⟨code, by simpa [BitFallbackZeroSampleImage.fallbackDecoderFamily] using hcode⟩)
      hcoverFallback

/-- Negative finite-cover form of the radius-zero fallback-probe lower bound. -/
theorem not_finitePredictorCover_of_fallback_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hN : N < Fintype.card Probe) :
    ¬ (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_fallback_injective_realization
      fallback target hinj hreal hcover)

/-- The same lower bound applies to finite representative-index covers of the
radius-zero wrapper. -/
theorem finiteIndexRepresentativeCover_card_le_of_fallback_injective_realization
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hrep :
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  have hrepFallback :
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N :=
    (BitFallbackZeroSampleImage.finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
      fallback).mp hrep
  exact
    exactVisible_finiteIndexRepresentativeCover_card_le_of_injective_realization
      (G := BitFallbackZeroSampleImage.fallbackDecoderFamily fallback)
      target hinj
      (by
        intro p
        rcases hreal p with ⟨code, hcode⟩
        exact ⟨code, by simpa [BitFallbackZeroSampleImage.fallbackDecoderFamily] using hcode⟩)
      hrepFallback

/-- Negative representative-index form of the radius-zero fallback-probe lower
bound. -/
theorem not_finiteIndexRepresentativeCover_of_fallback_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hN : N < Fintype.card Probe) :
    ¬ (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_fallback_injective_realization
      fallback target hinj hreal hrep)

/-- The same lower bound applies to finite quotient-code presentations of the
radius-zero wrapper. -/
theorem finitePredictorQuotient_card_le_of_fallback_injective_realization
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hquot :
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  have hquotFallback :
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorQuotient N :=
    (BitFallbackZeroSampleImage.finitePredictorQuotient_iff_fallbackDecoderFamily
      fallback).mp hquot
  exact
    exactVisible_finitePredictorQuotient_card_le_of_injective_realization
      (G := BitFallbackZeroSampleImage.fallbackDecoderFamily fallback)
      target hinj
      (by
        intro p
        rcases hreal p with ⟨code, hcode⟩
        exact ⟨code, by simpa [BitFallbackZeroSampleImage.fallbackDecoderFamily] using hcode⟩)
      hquotFallback

/-- Negative quotient-code form of the radius-zero fallback-probe lower bound. -/
theorem not_finitePredictorQuotient_of_fallback_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hN : N < Fintype.card Probe) :
    ¬ (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_fallback_injective_realization
      fallback target hinj hreal hquot)

/-- Exact visible compression at radius zero is impossible below the size of
any injectively realized fallback probe family. -/
theorem not_exactVisibleCompressionTarget_of_fallback_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget
      (Z := Z) (k := k)
      (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
      (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback) s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact
    not_finitePredictorCover_of_fallback_injective_realization_of_lt_card
      fallback target hinj hreal hs

/-- Clocked exact-visible realization at radius zero is impossible below the
size of any injectively realized fallback probe family. -/
theorem not_exists_clockedExactVisibleRealization_of_fallback_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {Z : Type v} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ code : BitCode fallbackBits, fallback code = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.zeroSampleWrapperFamily fallback).RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact
    not_finitePredictorCover_of_fallback_injective_realization_of_lt_card
      fallback target hinj hreal hs

end BitFallbackZeroSampleProbeObstruction

end Mettapedia.Computability.PNP
