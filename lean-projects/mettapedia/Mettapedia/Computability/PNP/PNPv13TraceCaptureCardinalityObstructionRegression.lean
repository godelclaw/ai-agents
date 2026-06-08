import Mettapedia.Computability.PNP.PNPv13TraceCaptureCardinalityObstruction

/-!
# Regression checks for the PNP v13 trace-capture cardinality obstruction
-/

namespace Mettapedia.Computability.PNP.PNPv13TraceCaptureCardinalityObstructionRegression

open Mettapedia.Computability.PNP

/-- Identity traces on all relevant states capture every Boolean observer. -/
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

theorem boolIdentityTraceSurface_traceOnRelevant_injective_regression :
    Function.Injective boolIdentityTraceSurface.traceOnRelevant := by
  exact
    (V13TraceCaptureSurface.capturesAllBoolObservers_iff_traceOnRelevant_injective
      boolIdentityTraceSurface).mp
      boolIdentityTraceSurface_capturesAllBoolObservers

theorem boolIdentityTraceSurface_relevantStateCard_le_traceCard_regression :
    Fintype.card (Subtype boolIdentityTraceSurface.targetRelevant) ≤
      Fintype.card Bool := by
  exact
    V13TraceCaptureSurface.relevantStateCard_le_traceCard_of_capturesAllBoolObservers
      (S := boolIdentityTraceSurface) inferInstance inferInstance
      boolIdentityTraceSurface_capturesAllBoolObservers

instance : Fintype V13ToyTraceState where
  elems := {.left, .right}
  complete := by
    intro s
    cases s <;> simp

noncomputable instance : Fintype (Subtype v13CollapsedTraceSurface.targetRelevant) :=
  Fintype.ofEquiv V13ToyTraceState
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

/-- Two relevant states collapsed to one trace already violate the new
cardinality lower bound. -/
theorem collapsed_trace_surface_not_capturesAllBoolObservers_of_cardinality_regression :
    ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact
    V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceCard_lt_relevantStateCard
      (S := v13CollapsedTraceSurface) inferInstance inferInstance
      (by
        simpa using (show 1 < Fintype.card V13ToyTraceState by decide))

/-- A two-trace alphabet cannot capture all Boolean observers on four
target-relevant states. -/
def fin4Fin2TraceSurface : V13TraceCaptureSurface (Fin 4) (Fin 2) where
  traceOf := fun _ => 0
  targetRelevant := fun _ => True

noncomputable instance : Fintype (Subtype fin4Fin2TraceSurface.targetRelevant) :=
  Fintype.ofEquiv (Fin 4)
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem fin4_fin2_trace_surface_not_capturesAllBoolObservers_regression :
    ¬ fin4Fin2TraceSurface.CapturesAllBoolObservers := by
  exact
    V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceCard_lt_relevantStateCard
      (S := fin4Fin2TraceSurface) inferInstance inferInstance
      (by
        have hcard :
            Fintype.card (Subtype fin4Fin2TraceSurface.targetRelevant) =
              Fintype.card (Fin 4) := by
          exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
        rw [hcard]
        decide)

end Mettapedia.Computability.PNP.PNPv13TraceCaptureCardinalityObstructionRegression
