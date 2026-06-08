import Mettapedia.Computability.PNP.ExactVisibleImageBudget
import Mettapedia.Computability.PNP.PNPv13TraceCaptureCardinalityObstruction

/-!
# PNP v13 trace-capture image-budget obstruction

`PNPv13TraceCaptureCardinalityObstruction.lean` shows that universal Boolean
trace capture forces injectivity on the target-relevant support.  This file
repackages the same pressure in the project's standard finite-image language:
the trace decoders themselves form an indexed predictor family on the relevant
support, so any universal capture theorem must realize the full Boolean
classifier space through that family.

Consequently a trace alphabet of size `|Trace|` can induce at most
`2^|Trace|` Boolean predictors on the target-relevant support.  If all Boolean
observers are captured, the target-relevant support therefore contributes the
full lower bound `2^|relevant support| ≤ 2^|Trace|`.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace V13TraceCaptureSurface

/-- The indexed family of Boolean predictors induced by choosing a Boolean
decoder on the trace alphabet and evaluating it on the target-relevant support.
-/
def traceDecoderFamily (S : V13TraceCaptureSurface State Trace) :
    IndexedPredictorFamily (Trace → Bool) (Subtype S.targetRelevant) where
  predict decode s := decode (S.traceOnRelevant s)

/-- If every Boolean observer on `State` factors through the trace, then every
Boolean classifier on the target-relevant support lies in the image of the
trace-decoder family. -/
theorem traceDecoderFamily_surjective_of_capturesAllBoolObservers
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    (hcapture : S.CapturesAllBoolObservers) :
    Function.Surjective (traceDecoderFamily S).predict := by
  classical
  intro target
  let observer : State → Bool := fun s =>
    if hs : S.targetRelevant s then
      target ⟨s, hs⟩
    else
      false
  rcases hcapture observer with ⟨decode, hdecode⟩
  refine ⟨decode, ?_⟩
  funext s
  simpa [traceDecoderFamily, observer, s.2] using hdecode s.1 s.2

/-- The full trace-decoder family is itself a finite cover of size
`2^|Trace|`: just enumerate all Boolean decoders on the trace alphabet. -/
theorem traceDecoderFamily_finitePredictorCover_traceClassifierCard
    (S : V13TraceCaptureSurface State Trace) [Fintype Trace] :
    (traceDecoderFamily S).FinitePredictorCover (2 ^ Fintype.card Trace) := by
  classical
  refine ⟨Finset.univ.image (traceDecoderFamily S).predict, ?_, ?_⟩
  · intro decode
    exact Finset.mem_image.mpr ⟨decode, Finset.mem_univ decode, rfl⟩
  · exact le_trans Finset.card_image_le (by simp [Fintype.card_bool])

/-- Universal Boolean trace capture forces the full Boolean classifier-space
inequality on the target-relevant support. -/
theorem boolClassifierCard_le_traceClassifierCard_of_capturesAllBoolObservers
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace]
    (hcapture : S.CapturesAllBoolObservers) :
    2 ^ Fintype.card (Subtype S.targetRelevant) ≤ 2 ^ Fintype.card Trace := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
      (G := traceDecoderFamily S)
      (traceDecoderFamily_surjective_of_capturesAllBoolObservers hcapture)
      (traceDecoderFamily_finitePredictorCover_traceClassifierCard S)

/-- So a trace alphabet whose Boolean decoder space is strictly smaller than
the full Boolean classifier space on the target-relevant support cannot capture
every Boolean observer. -/
theorem not_capturesAllBoolObservers_of_traceClassifierCard_lt
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace]
    (hcard :
      2 ^ Fintype.card Trace < 2 ^ Fintype.card (Subtype S.targetRelevant)) :
    ¬ S.CapturesAllBoolObservers := by
  intro hcapture
  exact Nat.not_le_of_lt hcard
    (boolClassifierCard_le_traceClassifierCard_of_capturesAllBoolObservers
      hcapture)

end V13TraceCaptureSurface

end Mettapedia.Computability.PNP
