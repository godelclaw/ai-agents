import Mettapedia.Computability.PNP.PNPv13CruxLedger

/-!
# PNP v13 trace-capture boundary

The v13 crux ledger asks for an adaptive-observer trace-capture theorem:
polynomial-time observers should reduce to finite CD evidence traces without
losing target-relevant advantage.  This file isolates the exact quotient
condition behind any such theorem.  An observer can be decoded from a trace
precisely when its output is constant on the target-relevant trace fibers.
Capturing every Boolean observer is therefore equivalent to having no
target-relevant trace collision.
-/

namespace Mettapedia.Computability.PNP

universe u v w

/-- Abstract trace-capture surface: a trace map plus the target-relevant states
on which downstream observers must be preserved. -/
structure V13TraceCaptureSurface (State : Type u) (Trace : Type v) where
  traceOf : State → Trace
  targetRelevant : State → Prop

namespace V13TraceCaptureSurface

/-- A decoder from traces correctly captures an observer on all target-relevant
states. -/
def ObserverTraceDecoderCorrect (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) (decode : Trace → Output) : Prop :=
  ∀ s, S.targetRelevant s → decode (S.traceOf s) = observer s

/-- An observer is trace-decodable when some trace decoder preserves it on all
target-relevant states. -/
def ObserverTraceDecodable (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) : Prop :=
  ∃ decode : Trace → Output, S.ObserverTraceDecoderCorrect observer decode

/-- The exact quotient condition: the observer is constant on every
target-relevant trace fiber. -/
def ObserverConstantOnTraceFibers (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) : Prop :=
  ∀ s₀ s₁, S.targetRelevant s₀ → S.targetRelevant s₁ →
    S.traceOf s₀ = S.traceOf s₁ → observer s₀ = observer s₁

/-- A same-trace observer conflict is a complete local certificate that the
observer has not been captured by the trace. -/
def ObserverSameTraceConflict (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) : Prop :=
  ∃ s₀ s₁, S.targetRelevant s₀ ∧ S.targetRelevant s₁ ∧
    S.traceOf s₀ = S.traceOf s₁ ∧ observer s₀ ≠ observer s₁

/-- A relevant trace collision forgets the identity of two target-relevant
states.  Such a collision blocks capture of all Boolean observers. -/
def RelevantTraceCollision (S : V13TraceCaptureSurface State Trace) : Prop :=
  ∃ s₀ s₁, S.targetRelevant s₀ ∧ S.targetRelevant s₁ ∧
    S.traceOf s₀ = S.traceOf s₁ ∧ s₀ ≠ s₁

/-- The strongest trace-capture endpoint for Boolean observers: every Boolean
observer on target-relevant states factors through the trace. -/
def CapturesAllBoolObservers (S : V13TraceCaptureSurface State Trace) : Prop :=
  ∀ observer : State → Bool, S.ObserverTraceDecodable observer

/-- Any correct trace decoder forces observer constancy on trace fibers. -/
theorem observerConstantOnTraceFibers_of_traceDecoderCorrect
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Output} {decode : Trace → Output}
    (hdecode : S.ObserverTraceDecoderCorrect observer decode) :
    S.ObserverConstantOnTraceFibers observer := by
  intro s₀ s₁ hs₀ hs₁ hsame
  calc
    observer s₀ = decode (S.traceOf s₀) := (hdecode s₀ hs₀).symm
    _ = decode (S.traceOf s₁) := by rw [hsame]
    _ = observer s₁ := hdecode s₁ hs₁

/-- Fiber constancy supplies a trace decoder, using an arbitrary default on
traces outside the target-relevant image. -/
theorem observerTraceDecodable_of_constantOnTraceFibers
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Output} [Inhabited Output]
    (hconstant : S.ObserverConstantOnTraceFibers observer) :
    S.ObserverTraceDecodable observer := by
  classical
  refine
    ⟨fun tr =>
      if h : ∃ s, S.targetRelevant s ∧ S.traceOf s = tr then
        observer (Classical.choose h)
      else default, ?_⟩
  intro s hs
  have h : ∃ s', S.targetRelevant s' ∧ S.traceOf s' = S.traceOf s :=
    ⟨s, hs, rfl⟩
  dsimp
  rw [dif_pos h]
  exact
    hconstant (Classical.choose h) s
      (Classical.choose_spec h).1 hs (Classical.choose_spec h).2

/-- Trace decodability is exactly observer constancy on the target-relevant
trace fibers. -/
theorem observerTraceDecodable_iff_constantOnTraceFibers
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) [Inhabited Output] :
    S.ObserverTraceDecodable observer ↔
      S.ObserverConstantOnTraceFibers observer := by
  constructor
  · rintro ⟨decode, hdecode⟩
    exact observerConstantOnTraceFibers_of_traceDecoderCorrect hdecode
  · exact observerTraceDecodable_of_constantOnTraceFibers

/-- Failure of fiber constancy exposes a same-trace observer conflict. -/
theorem observerSameTraceConflict_of_not_constantOnTraceFibers
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Output}
    (hfail : ¬ S.ObserverConstantOnTraceFibers observer) :
    S.ObserverSameTraceConflict observer := by
  classical
  by_cases hconf : S.ObserverSameTraceConflict observer
  · exact hconf
  · exfalso
    apply hfail
    intro s₀ s₁ hs₀ hs₁ hsame
    by_cases hout : observer s₀ = observer s₁
    · exact hout
    · exfalso
      exact hconf ⟨s₀, s₁, hs₀, hs₁, hsame, hout⟩

/-- A same-trace observer conflict refutes trace decodability. -/
theorem not_observerTraceDecodable_of_sameTraceConflict
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Output}
    (hconf : S.ObserverSameTraceConflict observer) :
    ¬ S.ObserverTraceDecodable observer := by
  rintro ⟨decode, hdecode⟩
  rcases hconf with ⟨s₀, s₁, hs₀, hs₁, hsame, hout⟩
  have hconstant :
      S.ObserverConstantOnTraceFibers observer :=
    observerConstantOnTraceFibers_of_traceDecoderCorrect hdecode
  exact hout (hconstant s₀ s₁ hs₀ hs₁ hsame)

/-- Non-decodability is exactly the presence of a same-trace observer conflict. -/
theorem not_observerTraceDecodable_iff_sameTraceConflict
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Output) [Inhabited Output] :
    ¬ S.ObserverTraceDecodable observer ↔
      S.ObserverSameTraceConflict observer := by
  constructor
  · intro hnot
    have hnotConstant :
        ¬ S.ObserverConstantOnTraceFibers observer := by
      intro hconstant
      exact hnot (observerTraceDecodable_of_constantOnTraceFibers hconstant)
    exact observerSameTraceConflict_of_not_constantOnTraceFibers hnotConstant
  · exact not_observerTraceDecodable_of_sameTraceConflict

/-- If every Boolean observer is trace-decodable, then the trace has no
target-relevant collisions. -/
theorem no_relevantTraceCollision_of_capturesAllBoolObservers
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    (hcapture : S.CapturesAllBoolObservers) :
    ¬ S.RelevantTraceCollision := by
  rintro ⟨s₀, s₁, hs₀, hs₁, hsame, hne⟩
  let observer : State → Bool := fun s => decide (s = s₀)
  have hconf : S.ObserverSameTraceConflict observer := by
    have hs₁ne : s₁ ≠ s₀ := fun h => hne h.symm
    refine ⟨s₀, s₁, hs₀, hs₁, hsame, ?_⟩
    simp [observer, hs₁ne]
  exact not_observerTraceDecodable_of_sameTraceConflict hconf (hcapture observer)

/-- A target-relevant trace collision blocks capture of all Boolean observers. -/
theorem not_capturesAllBoolObservers_of_relevantTraceCollision
    {S : V13TraceCaptureSurface State Trace} [DecidableEq State]
    (hcollision : S.RelevantTraceCollision) :
    ¬ S.CapturesAllBoolObservers := by
  intro hcapture
  exact no_relevantTraceCollision_of_capturesAllBoolObservers hcapture hcollision

/-- Capturing every Boolean observer is exactly collision-freeness on
target-relevant states. -/
theorem capturesAllBoolObservers_iff_not_relevantTraceCollision
    (S : V13TraceCaptureSurface State Trace) [DecidableEq State] :
    S.CapturesAllBoolObservers ↔ ¬ S.RelevantTraceCollision := by
  constructor
  · exact no_relevantTraceCollision_of_capturesAllBoolObservers
  · intro hno observer
    refine observerTraceDecodable_of_constantOnTraceFibers ?_
    intro s₀ s₁ hs₀ hs₁ hsame
    by_cases heq : s₀ = s₁
    · rw [heq]
    · exfalso
      exact hno ⟨s₀, s₁, hs₀, hs₁, hsame, heq⟩

end V13TraceCaptureSurface

/-- Two target-relevant states collapsed to one trace. -/
inductive V13ToyTraceState where
  | left
  | right
  deriving DecidableEq, Repr

/-- The collapsed toy trace surface maps both states to the same trace. -/
def v13CollapsedTraceSurface :
    V13TraceCaptureSurface V13ToyTraceState Unit where
  traceOf := fun _ => ()
  targetRelevant := fun _ => True

/-- A Boolean observer that separates the two collapsed states. -/
def v13ToyTraceObserver : V13ToyTraceState → Bool
  | .left => false
  | .right => true

/-- The toy observer has a same-trace conflict. -/
theorem v13CollapsedTraceSurface_sameTraceConflict :
    v13CollapsedTraceSurface.ObserverSameTraceConflict v13ToyTraceObserver := by
  refine ⟨.left, .right, trivial, trivial, rfl, ?_⟩
  simp [v13ToyTraceObserver]

/-- The toy observer cannot be decoded from the collapsed trace. -/
theorem v13CollapsedTraceSurface_not_observerTraceDecodable :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver := by
  exact
    V13TraceCaptureSurface.not_observerTraceDecodable_of_sameTraceConflict
      v13CollapsedTraceSurface_sameTraceConflict

/-- The collapsed toy trace surface has a target-relevant collision. -/
theorem v13CollapsedTraceSurface_relevantTraceCollision :
    v13CollapsedTraceSurface.RelevantTraceCollision := by
  refine ⟨.left, .right, trivial, trivial, rfl, ?_⟩
  simp

/-- Therefore the collapsed toy surface cannot capture all Boolean observers. -/
theorem v13CollapsedTraceSurface_not_capturesAllBoolObservers :
    ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact
    V13TraceCaptureSurface.not_capturesAllBoolObservers_of_relevantTraceCollision
      v13CollapsedTraceSurface_relevantTraceCollision

end Mettapedia.Computability.PNP
