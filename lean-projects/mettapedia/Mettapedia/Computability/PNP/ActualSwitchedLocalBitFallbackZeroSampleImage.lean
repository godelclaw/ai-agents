import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# PNP crux: the zero-sample bit fallback wrapper has exactly the fallback image

At sample radius zero, the bit-coded fallback wrapper does not merely preserve
surjectivity boundaries.  It has exactly the same predictor image as the raw
fallback decoder family itself.

This file packages that stronger structural fact and lifts it to the main
small-image interfaces used elsewhere in the route:

- finite predictor-image covers;
- exact visible compression targets;
- clocked exact-visible realizations.

So any zero-sample repair must prove genuine smallness of the fallback decoder
family.  The wrapper contributes no hidden compression content at all.
-/

namespace Mettapedia.Computability.PNP

universe v

namespace BitFallbackZeroSampleImage

/-- The raw exact-visible predictor family selected directly by the fallback
decoder. -/
def fallbackDecoderFamily
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleSwitchedFamily Z k (BitCode fallbackBits) where
  predict := fallback

@[simp] theorem fallbackDecoderFamily_predict
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (code : BitCode fallbackBits) :
    (fallbackDecoderFamily fallback).predict code = fallback code := rfl

/-- The index type of the zero-sample bit-coded fallback wrapper. -/
abbrev ZeroSampleIndex
    (Z : Type v) (k fallbackBits : ℕ) :=
  BoundedSampleFallbackFamilyIndex
    (ULift.{v} (BitCode fallbackBits))
    (ExactVisiblePostSwitchSurface Z k) 0

/-- The exact-visible predictor family of the zero-sample bit-coded fallback
wrapper. -/
noncomputable def zeroSampleWrapperFamily
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleSwitchedFamily Z k (ZeroSampleIndex Z k fallbackBits) :=
  (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
    Z k 0 fallbackBits fallback).predictorFamily

/-- At zero sample radius, every wrapper index already evaluates to the raw
fallback rule selected by its code. -/
theorem zeroSampleWrapper_predict_eq_fallback
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (index : ZeroSampleIndex Z k fallbackBits) :
    (zeroSampleWrapperFamily fallback).predict index = fallback index.1.down := by
  have hsample : index.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact Nat.eq_zero_of_le_zero index.2.2
  funext u
  simp [zeroSampleWrapperFamily,
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface,
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily, hsample]

/-- A rule is realized by the zero-sample wrapper exactly when it is realized
by the raw fallback decoder family. -/
theorem realizes_rule_iff_exists_fallbackCode
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index : ZeroSampleIndex Z k fallbackBits,
        (zeroSampleWrapperFamily fallback).predict index = rule) ↔
      ∃ code : BitCode fallbackBits, fallback code = rule := by
  constructor
  · rintro ⟨index, hindex⟩
    rw [zeroSampleWrapper_predict_eq_fallback fallback index] at hindex
    exact ⟨index.1.down, hindex⟩
  · rintro ⟨code, hcode⟩
    refine ⟨(ULift.up code, ⟨[], by simp⟩), ?_⟩
    simpa [hcode] using
      zeroSampleWrapper_predict_eq_fallback fallback
        (index := (ULift.up code, ⟨[], by simp⟩))

/-- The zero-sample wrapper and the raw fallback decoder family have exactly
the same finite predictor-image covers. -/
theorem finitePredictorCover_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FinitePredictorCover N ↔
      (fallbackDecoderFamily fallback).FinitePredictorCover N := by
  constructor
  · rintro ⟨S, hmem, hcard⟩
    refine ⟨S, ?_, hcard⟩
    intro code
    have hpredict := hmem (ULift.up code, ⟨[], by simp⟩)
    have heq :
        (zeroSampleWrapperFamily fallback).predict (ULift.up code, ⟨[], by simp⟩) =
          (fallbackDecoderFamily fallback).predict code := by
      simpa [fallbackDecoderFamily] using
        zeroSampleWrapper_predict_eq_fallback fallback
          (index := (ULift.up code, ⟨[], by simp⟩))
    rw [heq] at hpredict
    exact hpredict
  · rintro ⟨S, hmem, hcard⟩
    refine ⟨S, ?_, hcard⟩
    intro index
    rw [zeroSampleWrapper_predict_eq_fallback fallback index]
    exact hmem index.1.down

/-- The zero-sample wrapper and the raw fallback decoder family have exactly
the same finite representative-index covers. -/
theorem finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N ↔
      (fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N := by
  rw [← IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover,
    finitePredictorCover_iff_fallbackDecoderFamily,
    IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover]

/-- The zero-sample wrapper and the raw fallback decoder family have exactly
the same finite quotient-code presentations. -/
theorem finitePredictorQuotient_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FinitePredictorQuotient N ↔
      (fallbackDecoderFamily fallback).FinitePredictorQuotient N := by
  rw [← IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient,
    finitePredictorCover_iff_fallbackDecoderFamily,
    IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient]

/-- Radius-zero exact visible compression is equivalent to exact visible
compression of the raw fallback decoder family. -/
theorem exactVisibleCompressionTarget_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := ZeroSampleIndex Z k fallbackBits)
        (zeroSampleWrapperFamily fallback) s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitCode fallbackBits)
        (fallbackDecoderFamily fallback) s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover,
    exactVisibleCompressionTarget_iff_finitePredictorCover,
    finitePredictorCover_iff_fallbackDecoderFamily]

/-- The same equivalence holds for the clocked exact-visible realization
surface: radius zero adds no extra predictor-image compression content. -/
theorem exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
    {Z : Type v} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (zeroSampleWrapperFamily fallback).RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (fallbackDecoderFamily fallback).RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover,
    exists_clockedExactVisibleRealization_iff_finitePredictorCover,
    finitePredictorCover_iff_fallbackDecoderFamily]

end BitFallbackZeroSampleImage

end Mettapedia.Computability.PNP
