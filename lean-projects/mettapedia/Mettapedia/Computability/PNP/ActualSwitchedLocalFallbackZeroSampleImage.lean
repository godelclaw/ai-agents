import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# PNP crux: the zero-sample structured fallback wrapper has exactly the fallback image

At sample radius zero, the structured fallback wrapper does not merely preserve
surjectivity boundaries. It has exactly the same predictor image as the raw
fallback family itself.

This file packages that stronger structural fact and lifts it to the main
small-image interfaces used elsewhere in the route:

- finite predictor-image covers;
- exact visible compression targets;
- clocked exact-visible realizations.

So any zero-sample repair must prove genuine smallness of the fallback family.
The wrapper contributes no hidden compression content at all.
-/

namespace Mettapedia.Computability.PNP

universe v

namespace FallbackZeroSampleImage

/-- The raw exact-visible predictor family selected directly by the fallback
index. -/
def fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleSwitchedFamily Z k FallbackIndex where
  predict := fallback

@[simp] theorem fallbackFamily_predict
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (code : FallbackIndex) :
    (fallbackFamily fallback).predict code = fallback code := rfl

/-- The index type of the zero-sample structured fallback wrapper. -/
abbrev ZeroSampleIndex
    (FallbackIndex : Type v) (Z : Type v) (k : ℕ) :=
  BoundedSampleFallbackFamilyIndex
    FallbackIndex
    (ExactVisiblePostSwitchSurface Z k) 0

/-- The exact-visible predictor family of the zero-sample structured fallback
wrapper. -/
noncomputable def zeroSampleWrapperFamily
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleSwitchedFamily Z k (ZeroSampleIndex FallbackIndex Z k) :=
  (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
    FallbackIndex Z k 0 fallback).predictorFamily

/-- At zero sample radius, every wrapper index already evaluates to the raw
fallback rule selected by its code. -/
theorem zeroSampleWrapper_predict_eq_fallback
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index : ZeroSampleIndex FallbackIndex Z k) :
    (zeroSampleWrapperFamily fallback).predict index = fallback index.1 := by
  have hsample : index.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact Nat.eq_zero_of_le_zero index.2.2
  funext u
  simp [zeroSampleWrapperFamily,
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily, hsample]

/-- A rule is realized by the zero-sample wrapper exactly when it is realized
by the raw fallback family. -/
theorem realizes_rule_iff_exists_fallbackCode
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index : ZeroSampleIndex FallbackIndex Z k,
        (zeroSampleWrapperFamily fallback).predict index = rule) ↔
      ∃ code : FallbackIndex, fallback code = rule := by
  constructor
  · rintro ⟨index, hindex⟩
    rw [zeroSampleWrapper_predict_eq_fallback fallback index] at hindex
    exact ⟨index.1, hindex⟩
  · rintro ⟨code, hcode⟩
    refine ⟨(code, ⟨[], by simp⟩), ?_⟩
    simpa [hcode] using
      zeroSampleWrapper_predict_eq_fallback fallback
        (index := (code, ⟨[], by simp⟩))

/-- The zero-sample wrapper and the raw fallback family have exactly the same
finite predictor-image covers. -/
theorem finitePredictorCover_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FinitePredictorCover N ↔
      (fallbackFamily fallback).FinitePredictorCover N := by
  constructor
  · rintro ⟨S, hmem, hcard⟩
    refine ⟨S, ?_, hcard⟩
    intro code
    have hpredict := hmem (code, ⟨[], by simp⟩)
    have heq :
        (zeroSampleWrapperFamily fallback).predict (code, ⟨[], by simp⟩) =
          (fallbackFamily fallback).predict code := by
      simpa [fallbackFamily] using
        zeroSampleWrapper_predict_eq_fallback fallback
          (index := (code, ⟨[], by simp⟩))
    rw [heq] at hpredict
    exact hpredict
  · rintro ⟨S, hmem, hcard⟩
    refine ⟨S, ?_, hcard⟩
    intro index
    rw [zeroSampleWrapper_predict_eq_fallback fallback index]
    exact hmem index.1

/-- The zero-sample wrapper and the raw fallback family have exactly the same
finite representative-index covers. -/
theorem finiteIndexRepresentativeCover_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FiniteIndexRepresentativeCover N ↔
      (fallbackFamily fallback).FiniteIndexRepresentativeCover N := by
  rw [← IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover,
    finitePredictorCover_iff_fallbackFamily,
    IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover]

/-- The zero-sample wrapper and the raw fallback family have exactly the same
finite quotient-code presentations. -/
theorem finitePredictorQuotient_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (zeroSampleWrapperFamily fallback).FinitePredictorQuotient N ↔
      (fallbackFamily fallback).FinitePredictorQuotient N := by
  rw [← IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient,
    finitePredictorCover_iff_fallbackFamily,
    IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient]

/-- Radius-zero exact visible compression is equivalent to exact visible
compression of the raw fallback family. -/
theorem exactVisibleCompressionTarget_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k s : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := ZeroSampleIndex FallbackIndex Z k)
        (zeroSampleWrapperFamily fallback) s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackIndex)
        (fallbackFamily fallback) s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover,
    exactVisibleCompressionTarget_iff_finitePredictorCover,
    finitePredictorCover_iff_fallbackFamily]

/-- The same equivalence holds for the clocked exact-visible realization
surface: radius zero adds no extra predictor-image compression content. -/
theorem exists_clockedExactVisibleRealization_iff_fallbackFamily
    {FallbackIndex : Type v} {Z : Type v} {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (zeroSampleWrapperFamily fallback).RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (fallbackFamily fallback).RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover,
    exists_clockedExactVisibleRealization_iff_finitePredictorCover,
    finitePredictorCover_iff_fallbackFamily]

end FallbackZeroSampleImage

end Mettapedia.Computability.PNP
