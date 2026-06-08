import Mathlib.Data.Fintype.Card
import Mettapedia.Computability.PNP.PNPv13TraceCapture

/-!
# PNP v13 trace-capture cardinality obstruction

`PNPv13TraceCapture.lean` isolates the exact quotient condition for universal
Boolean observer capture.  This file turns that condition into a finite-cardinal
obstruction: once every Boolean observer factors through the trace, the trace
map must already be injective on the target-relevant support.

Therefore any finite trace alphabet used to encode all target-relevant Boolean
observers must be at least as large as the target-relevant state set itself.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace V13TraceCaptureSurface

/-- The trace map restricted to the target-relevant support. -/
def traceOnRelevant (S : V13TraceCaptureSurface State Trace) :
    Subtype S.targetRelevant → Trace := fun s => S.traceOf s.1

/-- If the target-relevant trace fibers are collision-free, then the restricted
trace map is injective on the target-relevant support. -/
theorem traceOnRelevant_injective_of_no_relevantTraceCollision
    {S : V13TraceCaptureSurface State Trace}
    (hno : ¬ S.RelevantTraceCollision) :
    Function.Injective S.traceOnRelevant := by
  intro s₀ s₁ hsame
  apply Subtype.ext
  by_cases hne : s₀.1 = s₁.1
  · exact hne
  · exfalso
    exact hno ⟨s₀.1, s₁.1, s₀.2, s₁.2, hsame, hne⟩

/-- Conversely, injectivity of the restricted trace map rules out target-
relevant trace collisions. -/
theorem no_relevantTraceCollision_of_traceOnRelevant_injective
    {S : V13TraceCaptureSurface State Trace}
    (hinj : Function.Injective S.traceOnRelevant) :
    ¬ S.RelevantTraceCollision := by
  rintro ⟨s₀, s₁, hs₀, hs₁, hsame, hne⟩
  have hsub :
      (⟨s₀, hs₀⟩ : {s : State // S.targetRelevant s}) =
        ⟨s₁, hs₁⟩ := hinj hsame
  exact hne (congrArg Subtype.val hsub)

/-- Universal Boolean trace capture is equivalent to injectivity of the trace
map on the target-relevant support. -/
theorem capturesAllBoolObservers_iff_traceOnRelevant_injective
    (S : V13TraceCaptureSurface State Trace) [DecidableEq State] :
    S.CapturesAllBoolObservers ↔ Function.Injective S.traceOnRelevant := by
  rw [capturesAllBoolObservers_iff_not_relevantTraceCollision]
  constructor
  · exact traceOnRelevant_injective_of_no_relevantTraceCollision
  · exact no_relevantTraceCollision_of_traceOnRelevant_injective

/-- Any finite trace alphabet that captures all Boolean observers must have
cardinality at least the target-relevant state count. -/
theorem relevantStateCard_le_traceCard_of_capturesAllBoolObservers
    {State : Type u} {Trace : Type v}
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    (instRelevant : Fintype (Subtype S.targetRelevant)) (instTrace : Fintype Trace)
    (hcapture : S.CapturesAllBoolObservers) :
    Fintype.card (Subtype S.targetRelevant) ≤ Fintype.card Trace := by
  letI := instRelevant
  letI := instTrace
  exact
    Fintype.card_le_of_injective S.traceOnRelevant
      ((capturesAllBoolObservers_iff_traceOnRelevant_injective S).mp hcapture)

/-- So universal Boolean trace capture is impossible once the trace alphabet is
strictly smaller than the target-relevant state set. -/
theorem not_capturesAllBoolObservers_of_traceCard_lt_relevantStateCard
    {State : Type u} {Trace : Type v}
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    (instRelevant : Fintype (Subtype S.targetRelevant)) (instTrace : Fintype Trace)
    (hcard : Fintype.card Trace < Fintype.card (Subtype S.targetRelevant)) :
    ¬ S.CapturesAllBoolObservers := by
  letI := instRelevant
  letI := instTrace
  intro hcapture
  exact
    Nat.not_le_of_lt hcard
      (relevantStateCard_le_traceCard_of_capturesAllBoolObservers
        (S := S) instRelevant instTrace hcapture)

end V13TraceCaptureSurface

end Mettapedia.Computability.PNP
