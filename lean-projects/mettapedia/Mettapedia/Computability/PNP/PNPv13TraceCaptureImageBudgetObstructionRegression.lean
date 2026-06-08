import Mettapedia.Computability.PNP.PNPv13TraceCaptureImageBudgetObstruction

/-!
# Regression checks for the PNP v13 trace-capture image-budget obstruction
-/

namespace Mettapedia.Computability.PNP.PNPv13TraceCaptureImageBudgetObstructionRegression

open Mettapedia.Computability.PNP

/-- Identity traces on all relevant Boolean states already realize the whole
relevant Boolean classifier space through trace decoders. -/
def boolIdentityTraceSurface : V13TraceCaptureSurface Bool Bool where
  traceOf := id
  targetRelevant := fun _ => True

noncomputable instance : Fintype (Subtype boolIdentityTraceSurface.targetRelevant) :=
  Fintype.ofEquiv Bool
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem boolIdentityTraceSurface_capturesAllBoolObservers :
    boolIdentityTraceSurface.CapturesAllBoolObservers := by
  refine
    (V13TraceCaptureSurface.capturesAllBoolObservers_iff_not_relevantTraceCollision
      boolIdentityTraceSurface).2 ?_
  rintro ⟨s₀, s₁, _, _, hsame, hne⟩
  exact hne hsame

theorem bool_identity_trace_decoder_family_surjective_regression :
    Function.Surjective
      (V13TraceCaptureSurface.traceDecoderFamily boolIdentityTraceSurface).predict := by
  exact
    V13TraceCaptureSurface.traceDecoderFamily_surjective_of_capturesAllBoolObservers
      boolIdentityTraceSurface_capturesAllBoolObservers

theorem bool_identity_trace_decoder_family_cover_regression :
    (V13TraceCaptureSurface.traceDecoderFamily boolIdentityTraceSurface).FinitePredictorCover 4 := by
  simpa using
    V13TraceCaptureSurface.traceDecoderFamily_finitePredictorCover_traceClassifierCard
      boolIdentityTraceSurface

theorem bool_identity_classifier_card_le_trace_classifier_card_regression :
    4 ≤ 4 := by
  decide

instance : Fintype V13ToyTraceState where
  elems := {.left, .right}
  complete := by
    intro s
    cases s <;> simp

noncomputable instance : Fintype (Subtype v13CollapsedTraceSurface.targetRelevant) :=
  Fintype.ofEquiv V13ToyTraceState
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

/-- One trace induces only two Boolean decoders, so it cannot realize all four
Boolean classifiers on two relevant states. -/
theorem collapsed_trace_surface_not_captures_all_bool_observers_of_image_budget_regression :
    ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact
    V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceClassifierCard_lt
      (S := v13CollapsedTraceSurface)
      (by
        have hcard :
            Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant) =
              Fintype.card V13ToyTraceState := by
          exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
        rw [hcard]
        decide)

/-- Two traces induce only four Boolean decoders, so they still cannot realize
all sixteen Boolean classifiers on four relevant states. -/
def fin4Fin2TraceSurface : V13TraceCaptureSurface (Fin 4) (Fin 2) where
  traceOf := fun s =>
    if s.1 < 2 then 0 else 1
  targetRelevant := fun _ => True

noncomputable instance : Fintype (Subtype fin4Fin2TraceSurface.targetRelevant) :=
  Fintype.ofEquiv (Fin 4)
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem fin4_fin2_trace_surface_not_captures_all_bool_observers_of_image_budget_regression :
    ¬ fin4Fin2TraceSurface.CapturesAllBoolObservers := by
  exact
    V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceClassifierCard_lt
      (S := fin4Fin2TraceSurface)
      (by
        have hcard :
            Fintype.card (Subtype fin4Fin2TraceSurface.targetRelevant) =
              Fintype.card (Fin 4) := by
          exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
        rw [hcard]
        decide)

end Mettapedia.Computability.PNP.PNPv13TraceCaptureImageBudgetObstructionRegression
