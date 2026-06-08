import Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCapture

/-!
# Regression checks for PNP v13 random-coin trace capture
-/

namespace Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCaptureRegression

open Mettapedia.Computability.PNP

universe u v w z

theorem random_observer_decodable_iff_coinwise_observer_decodable_regression
    {State : Type u} {Trace : Type v} {Coin : Type w} {Output : Type z}
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) :
    S.RandomObserverTraceDecodable observer ↔
      ∀ c, S.ObserverTraceDecodable (fun s => observer s c) := by
  exact
    V13TraceCaptureSurface.randomObserverTraceDecodable_iff_forall_coin_observerTraceDecodable
      S observer

theorem random_observer_decodable_iff_coinwise_constant_regression
    {State : Type u} {Trace : Type v} {Coin : Type w} {Output : Type z}
    [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) :
    S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverConstantOnTraceFibers observer := by
  exact
    V13TraceCaptureSurface.randomObserverTraceDecodable_iff_constantOnTraceFibers
      S observer

theorem random_observer_not_decodable_iff_coinwise_conflict_regression
    {State : Type u} {Trace : Type v} {Coin : Type w} {Output : Type z}
    [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output) :
    ¬ S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverSameTraceConflict observer := by
  exact
    V13TraceCaptureSurface.not_randomObserverTraceDecodable_iff_sameTraceConflict
      S observer

theorem bool_random_observer_decodable_of_captures_all_bool_observers_regression
    {State : Type u} {Trace : Type v} {Coin : Type w}
    {S : V13TraceCaptureSurface State Trace}
    (hcapture : S.CapturesAllBoolObservers)
    (observer : State → Coin → Bool) :
    S.RandomObserverTraceDecodable observer := by
  exact
    V13TraceCaptureSurface.randomObserverTraceDecodable_of_capturesAllBoolObservers
      hcapture observer

theorem collapsed_random_trace_surface_same_trace_conflict_regression :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
      v13ToyRandomTraceObserver := by
  exact v13CollapsedTraceSurface_randomSameTraceConflict

theorem collapsed_random_trace_surface_not_observer_decodable_regression :
    ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
      v13ToyRandomTraceObserver := by
  exact v13CollapsedTraceSurface_not_randomObserverTraceDecodable

end Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCaptureRegression
