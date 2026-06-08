import Mettapedia.Computability.PNP.PNPv13TraceCapture

/-!
# PNP v13 random-coin trace-capture boundary

The v13 trace-capture section also invokes random coins and deterministic
reductions.  This file isolates the finite logical content of that step:
capturing a randomized observer is exactly capturing every deterministic coin
slice.  Random coins therefore do not repair a target-relevant trace collision;
they only index a family of deterministic trace-capture obligations.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

namespace V13TraceCaptureSurface

/-- A trace decoder correctly captures a coin-indexed observer when it preserves
the observer output for every target-relevant state and every coin value. -/
def RandomObserverTraceDecoderCorrect
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output)
    (decode : Trace → Coin → Output) : Prop :=
  ∀ s c, S.targetRelevant s → decode (S.traceOf s) c = observer s c

/-- A randomized observer is trace-decodable when a trace/coin decoder
preserves all of its deterministic coin slices. -/
def RandomObserverTraceDecodable
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) : Prop :=
  ∃ decode : Trace → Coin → Output,
    S.RandomObserverTraceDecoderCorrect observer decode

/-- The coinwise quotient condition for randomized observers. -/
def RandomObserverConstantOnTraceFibers
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) : Prop :=
  ∀ c s₀ s₁, S.targetRelevant s₀ → S.targetRelevant s₁ →
    S.traceOf s₀ = S.traceOf s₁ → observer s₀ c = observer s₁ c

/-- A same-trace conflict for one coin value is a complete local refuter of
randomized-observer trace capture. -/
def RandomObserverSameTraceConflict
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) : Prop :=
  ∃ c s₀ s₁, S.targetRelevant s₀ ∧ S.targetRelevant s₁ ∧
    S.traceOf s₀ = S.traceOf s₁ ∧ observer s₀ c ≠ observer s₁ c

/-- Randomized trace decodability is exactly deterministic trace decodability
for every coin slice. -/
theorem randomObserverTraceDecodable_iff_forall_coin_observerTraceDecodable
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) :
    S.RandomObserverTraceDecodable observer ↔
      ∀ c, S.ObserverTraceDecodable (fun s => observer s c) := by
  constructor
  · rintro ⟨decode, hdecode⟩ c
    exact ⟨fun tr => decode tr c, fun s hs => hdecode s c hs⟩
  · intro hcoin
    classical
    refine ⟨fun tr c => Classical.choose (hcoin c) tr, ?_⟩
    intro s c hs
    exact Classical.choose_spec (hcoin c) s hs

/-- Randomized trace decodability is exactly coinwise constancy on
target-relevant trace fibers. -/
theorem randomObserverTraceDecodable_iff_constantOnTraceFibers
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) [Inhabited Output] :
    S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverConstantOnTraceFibers observer := by
  rw [randomObserverTraceDecodable_iff_forall_coin_observerTraceDecodable]
  constructor
  · intro hcoin c
    exact
      (observerTraceDecodable_iff_constantOnTraceFibers
        S (fun s => observer s c)).mp (hcoin c)
  · intro hconstant c
    exact
      (observerTraceDecodable_iff_constantOnTraceFibers
        S (fun s => observer s c)).mpr (hconstant c)

/-- A deterministic capture theorem for every Boolean observer immediately
captures every Boolean randomized observer coin-slice by coin-slice. -/
theorem randomObserverTraceDecodable_of_capturesAllBoolObservers
    {S : V13TraceCaptureSurface State Trace}
    (hcapture : S.CapturesAllBoolObservers)
    (observer : State → Coin → Bool) :
    S.RandomObserverTraceDecodable observer := by
  exact
    (randomObserverTraceDecodable_iff_forall_coin_observerTraceDecodable
      S observer).mpr (fun c => hcapture (fun s => observer s c))

/-- A same-trace conflict in one coin slice blocks randomized trace
decodability. -/
theorem not_randomObserverTraceDecodable_of_sameTraceConflict
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Coin → Output}
    (hconf : S.RandomObserverSameTraceConflict observer) :
    ¬ S.RandomObserverTraceDecodable observer := by
  rintro ⟨decode, hdecode⟩
  rcases hconf with ⟨c, s₀, s₁, hs₀, hs₁, hsame, hout⟩
  have hslice :
      S.ObserverTraceDecoderCorrect
        (fun s => observer s c) (fun tr => decode tr c) := by
    intro s hs
    exact hdecode s c hs
  have hconstant :
      S.ObserverConstantOnTraceFibers (fun s => observer s c) :=
    observerConstantOnTraceFibers_of_traceDecoderCorrect hslice
  exact hout (hconstant s₀ s₁ hs₀ hs₁ hsame)

/-- Failure of coinwise trace-fiber constancy exposes a same-trace conflict at
one coin value. -/
theorem randomObserverSameTraceConflict_of_not_constantOnTraceFibers
    {S : V13TraceCaptureSurface State Trace}
    {observer : State → Coin → Output}
    (hfail : ¬ S.RandomObserverConstantOnTraceFibers observer) :
    S.RandomObserverSameTraceConflict observer := by
  classical
  by_cases hconf : S.RandomObserverSameTraceConflict observer
  · exact hconf
  · exfalso
    apply hfail
    intro c s₀ s₁ hs₀ hs₁ hsame
    by_cases hout : observer s₀ c = observer s₁ c
    · exact hout
    · exfalso
      exact hconf ⟨c, s₀, s₁, hs₀, hs₁, hsame, hout⟩

/-- Non-decodability of a randomized observer is exactly a same-trace conflict
in one deterministic coin slice. -/
theorem not_randomObserverTraceDecodable_iff_sameTraceConflict
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) [Inhabited Output] :
    ¬ S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverSameTraceConflict observer := by
  constructor
  · intro hnot
    have hnotConstant :
        ¬ S.RandomObserverConstantOnTraceFibers observer := by
      intro hconstant
      exact hnot
        ((randomObserverTraceDecodable_iff_constantOnTraceFibers
          S observer).mpr hconstant)
    exact randomObserverSameTraceConflict_of_not_constantOnTraceFibers hnotConstant
  · exact not_randomObserverTraceDecodable_of_sameTraceConflict

end V13TraceCaptureSurface

/-- A randomized observer that separates the two collapsed toy trace states on
every coin slice. -/
def v13ToyRandomTraceObserver : V13ToyTraceState → Bool → Bool
  | .left, _ => false
  | .right, _ => true

/-- The collapsed trace surface has a same-trace conflict for the randomized
toy observer. -/
theorem v13CollapsedTraceSurface_randomSameTraceConflict :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
      v13ToyRandomTraceObserver := by
  refine ⟨false, .left, .right, trivial, trivial, rfl, ?_⟩
  simp [v13ToyRandomTraceObserver]

/-- The randomized toy observer cannot be decoded from the collapsed trace. -/
theorem v13CollapsedTraceSurface_not_randomObserverTraceDecodable :
    ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
      v13ToyRandomTraceObserver := by
  exact
    V13TraceCaptureSurface.not_randomObserverTraceDecodable_of_sameTraceConflict
      v13CollapsedTraceSurface_randomSameTraceConflict

end Mettapedia.Computability.PNP
