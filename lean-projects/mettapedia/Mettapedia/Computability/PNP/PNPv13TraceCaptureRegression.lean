import Mettapedia.Computability.PNP.PNPv13TraceCapture

/-!
# Regression checks for the PNP v13 trace-capture boundary
-/

namespace Mettapedia.Computability.PNP.PNPv13TraceCaptureRegression

open Mettapedia.Computability.PNP

universe u v w

theorem observer_decodable_iff_constant_on_trace_fibers_regression
    {State : Type u} {Trace : Type v} {Output : Type w}
    [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace) (observer : State → Output) :
    S.ObserverTraceDecodable observer ↔
      S.ObserverConstantOnTraceFibers observer := by
  exact V13TraceCaptureSurface.observerTraceDecodable_iff_constantOnTraceFibers
    S observer

theorem observer_not_decodable_iff_same_trace_conflict_regression
    {State : Type u} {Trace : Type v} {Output : Type w}
    [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace) (observer : State → Output) :
    ¬ S.ObserverTraceDecodable observer ↔
      S.ObserverSameTraceConflict observer := by
  exact V13TraceCaptureSurface.not_observerTraceDecodable_iff_sameTraceConflict
    S observer

theorem captures_all_bool_observers_iff_no_relevant_collision_regression
    {State : Type u} {Trace : Type v} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace) :
    S.CapturesAllBoolObservers ↔ ¬ S.RelevantTraceCollision := by
  exact V13TraceCaptureSurface.capturesAllBoolObservers_iff_not_relevantTraceCollision S

theorem collapsed_trace_surface_same_trace_conflict_regression :
    v13CollapsedTraceSurface.ObserverSameTraceConflict v13ToyTraceObserver := by
  exact v13CollapsedTraceSurface_sameTraceConflict

theorem collapsed_trace_surface_not_observer_decodable_regression :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver := by
  exact v13CollapsedTraceSurface_not_observerTraceDecodable

theorem collapsed_trace_surface_relevant_collision_regression :
    v13CollapsedTraceSurface.RelevantTraceCollision := by
  exact v13CollapsedTraceSurface_relevantTraceCollision

theorem collapsed_trace_surface_not_captures_all_bool_observers_regression :
    ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact v13CollapsedTraceSurface_not_capturesAllBoolObservers

end Mettapedia.Computability.PNP.PNPv13TraceCaptureRegression
