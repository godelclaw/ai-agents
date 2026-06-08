import Mettapedia.Computability.PNP.PNPv13RouteSynthesis

/-!
# Forced-step obstructions for the PNP v13 switching route

The repeated-pivot blocker rules out literal reuse of a positive-mass success
event.  This file records the broader finite-count obstruction: once the
accumulated success history has positive mass, any next success event already
forced by that history cannot be a conditional half-step.  This blocks
renaming or refactoring a repeated pivot into a logically implied later event.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- If all events in `hist` hold and the next event also holds, then every
event in `hist ++ [event]` holds. -/
theorem allEvents_append_singleton_of_event {Ω : Type u}
    (hist : List (FiniteEvent Ω)) (event : FiniteEvent Ω) {ω : Ω}
    (hhist : allEvents hist ω) (hevent : event.pred ω) :
    allEvents (hist ++ [event]) ω := by
  induction hist with
  | nil =>
      exact ⟨hevent, trivial⟩
  | cons head tail ih =>
      exact ⟨hhist.1, ih hhist.2⟩

/-- If the accumulated history pointwise implies the next event, adding that
event leaves the finite history count unchanged. -/
theorem finiteHistoryCount_append_singleton_eq_of_history_imp_event
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {event : FiniteEvent Ω}
    (himp : ∀ ω, allEvents hist ω → event.pred ω) :
    finiteHistoryCount Ω (hist ++ [event]) = finiteHistoryCount Ω hist := by
  apply le_antisymm
  · exact finiteHistoryCount_append_le (Ω := Ω) hist [event]
  · simpa [finiteHistoryCount] using
      finiteEventCount_le_of_imp (Ω := Ω)
        (E := allEvents hist) (F := allEvents (hist ++ [event]))
        (fun ω hhist =>
          allEvents_append_singleton_of_event hist event hhist
            (himp ω hhist))

/-- A positive current history cannot be halved by an event already forced by
that history. -/
theorem not_prefixHalfStep_of_history_imp_event_of_positive
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {event : FiniteEvent Ω}
    (hpos : 0 < finiteHistoryCount Ω hist)
    (himp : ∀ ω, allEvents hist ω → event.pred ω) :
    ¬ PrefixHalfStep hist event := by
  intro hhalf
  have heq :
      finiteHistoryCount Ω (hist ++ [event]) =
        finiteHistoryCount Ω hist :=
    finiteHistoryCount_append_singleton_eq_of_history_imp_event
      (Ω := Ω) (hist := hist) (event := event) himp
  have hlt :
      finiteHistoryCount Ω hist < 2 * finiteHistoryCount Ω hist := by
    nth_rewrite 1 [← Nat.one_mul (finiteHistoryCount Ω hist)]
    exact Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hpos
  have hle :
      2 * finiteHistoryCount Ω hist ≤ finiteHistoryCount Ω hist := by
    simpa [PrefixHalfStep, heq] using hhalf
  exact (not_le_of_gt hlt) hle

/-- Failure of a later prefix half-step blocks the whole abstract v13
switching list at that position. -/
theorem not_v13SwitchingInstantiatedFrom_append_cons_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13SwitchedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13SwitchedStep Ω)}
    (hfail :
      ¬ PrefixHalfStep (hist ++ v13SuccessEvents pre) step.successEvent) :
    ¬ V13SwitchingInstantiatedFrom hist (pre ++ step :: suffix) := by
  induction pre generalizing hist with
  | nil =>
      have hfail' : ¬ PrefixHalfStep hist step.successEvent := by
        simpa [v13SuccessEvents] using hfail
      exact not_v13SwitchingInstantiatedFrom_cons_of_not_prefixHalfStep
        (hist := hist) (step := step) (rest := suffix) hfail'
  | cons head tail ih =>
      intro h
      have hfail' :
          ¬ PrefixHalfStep
              ((hist ++ [head.successEvent]) ++ v13SuccessEvents tail)
              step.successEvent := by
        simpa [v13SuccessEvents, List.append_assoc] using hfail
      exact ih (hist := hist ++ [head.successEvent]) hfail' h.2

/-- A switched list has a forced positive step when some later success event is
already implied by the accumulated success history and that history still has
positive mass. -/
def V13ForcedPositiveStepFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω)) : Prop :=
  ∃ pre step suffix,
    steps = pre ++ step :: suffix ∧
      0 < finiteHistoryCount Ω (hist ++ v13SuccessEvents pre) ∧
      ∀ ω, allEvents (hist ++ v13SuccessEvents pre) ω →
        step.successEvent.pred ω

/-- If an explicit later switched step is forced on a positive accumulated
history, the abstract v13 switching certificate cannot instantiate the list. -/
theorem not_v13SwitchingInstantiatedFrom_forcedPositiveStep_at
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13SwitchedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13SwitchedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ v13SuccessEvents pre))
    (himp : ∀ ω, allEvents (hist ++ v13SuccessEvents pre) ω →
      step.successEvent.pred ω) :
    ¬ V13SwitchingInstantiatedFrom hist (pre ++ step :: suffix) := by
  exact
    not_v13SwitchingInstantiatedFrom_append_cons_of_not_prefixHalfStep
      (hist := hist) (pre := pre) (step := step) (suffix := suffix)
      (not_prefixHalfStep_of_history_imp_event_of_positive hpos himp)

/-- Route-class form for abstract v13 switched steps. -/
theorem not_v13SwitchingInstantiatedFrom_of_forcedPositiveStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hforced : V13ForcedPositiveStepFrom hist steps) :
    ¬ V13SwitchingInstantiatedFrom hist steps := by
  rcases hforced with ⟨pre, step, suffix, hsteps, hpos, himp⟩
  rw [hsteps]
  exact
    not_v13SwitchingInstantiatedFrom_forcedPositiveStep_at
      (hist := hist) (pre := pre) (step := step) (suffix := suffix)
      hpos himp

/-- Forced positive steps also block the existential concrete-cell v13
interface, since concrete certificates imply abstract certificates. -/
theorem not_v13ConcreteSwitchingInstantiatedFrom_of_forcedPositiveStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hforced : V13ForcedPositiveStepFrom hist steps) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist steps := by
  intro h
  exact not_v13SwitchingInstantiatedFrom_of_forcedPositiveStep hforced
    (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)

/-- Fixed-field version of the forced positive step route-class assumption. -/
def V13ForcedPositiveFieldedStepFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∃ pre item suffix,
    items = pre ++ item :: suffix ∧
      0 < finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents pre) ∧
      ∀ ω, allEvents (hist ++ v13FieldedSuccessEvents pre) ω →
        item.step.successEvent.pred ω

/-- If an explicit later fixed-field step is forced on a positive accumulated
history, the fixed-field certificate cannot instantiate the list. -/
theorem not_v13FieldSwitchingInstantiatedFrom_forcedPositiveFieldedStep_at
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents pre))
    (himp : ∀ ω, allEvents (hist ++ v13FieldedSuccessEvents pre) ω →
      item.step.successEvent.pred ω) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  have hfailHalf :
      ¬ PrefixHalfStep (hist ++ v13FieldedSuccessEvents pre)
        item.step.successEvent :=
    not_prefixHalfStep_of_history_imp_event_of_positive hpos himp
  have hfailCert :
      ¬ V13FieldPrefixInstantiation item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step := by
    intro cert
    exact hfailHalf (prefixHalfStep_of_v13FieldPrefixInstantiation cert)
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      hfailCert

/-- Route-class form for fixed-field v13 switching certificates. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_forcedPositiveFieldedStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hforced : V13ForcedPositiveFieldedStepFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  rcases hforced with ⟨pre, item, suffix, hitems, hpos, himp⟩
  rw [hitems]
  exact
    not_v13FieldSwitchingInstantiatedFrom_forcedPositiveFieldedStep_at
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      hpos himp

/-- The same forced-step obstruction blocks the operational same-cell matching
formulation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_of_forcedPositiveFieldedStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hforced : V13ForcedPositiveFieldedStepFrom hist items) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  intro hmatch
  exact not_v13FieldSwitchingInstantiatedFrom_of_forcedPositiveFieldedStep
    hforced (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- Synthesis form: a forced positive fixed-field step blocks both fielded v13
route formulations. -/
theorem v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hforced : V13ForcedPositiveFieldedStepFrom hist items) :
    (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_forcedPositiveFieldedStep
        hforced,
      not_v13FieldSwitchingFailureMatchingFrom_of_forcedPositiveFieldedStep
        hforced⟩

section BoolPairForcedDiagonal

/-- Exact success for the second Boolean coordinate. -/
def v13BoolPairSecondCoordinateStep : V13SwitchedStep (Bool × Bool) where
  coordinate := 1
  observerBit := fun ω => ω.2
  targetBit := fun _ => true

/-- Exact success for the Boolean-square diagonal.  This success event is
globally half-mass, but it becomes forced after first- and second-coordinate
success are both imposed. -/
def v13BoolPairDiagonalStep : V13SwitchedStep (Bool × Bool) where
  coordinate := 2
  observerBit := fun ω => decide (ω.1 = ω.2)
  targetBit := fun _ => true

/-- The second-coordinate success event has numerator `2` on the Boolean
square. -/
theorem v13BoolPairSecondCoordinateStep_success_count :
    finiteHistoryCount (Bool × Bool)
      [v13BoolPairSecondCoordinateStep.successEvent] = 2 := by
  decide

/-- The diagonal success event has numerator `2` on the Boolean square. -/
theorem v13BoolPairDiagonalStep_success_count :
    finiteHistoryCount (Bool × Bool)
      [v13BoolPairDiagonalStep.successEvent] = 2 := by
  decide

/-- The first-coordinate and second-coordinate success events leave exactly one
Boolean-square point. -/
theorem v13BoolPairFirstSecond_success_count :
    finiteHistoryCount (Bool × Bool)
      [v13BoolPairRepeatedStep.successEvent,
        v13BoolPairSecondCoordinateStep.successEvent] = 1 := by
  decide

/-- The second success cut is still a valid half-step after the first one. -/
theorem prefixHalfStep_v13BoolPairSecondCoordinateStep_after_first :
    PrefixHalfStep [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairSecondCoordinateStep.successEvent := by
  rw [PrefixHalfStep]
  decide

/-- The diagonal success event is globally half-admissible from the empty
history. -/
theorem prefixHalfStep_v13BoolPairDiagonalStep_empty :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairDiagonalStep.successEvent := by
  rw [PrefixHalfStep]
  decide

/-- After first- and second-coordinate success, diagonal success is logically
forced. -/
theorem v13BoolPairFirstSecond_forcesDiagonal :
    ∀ ω, allEvents
      [v13BoolPairRepeatedStep.successEvent,
        v13BoolPairSecondCoordinateStep.successEvent] ω →
      v13BoolPairDiagonalStep.successEvent.pred ω := by
  intro ω hω
  cases ω with
  | mk first second =>
      cases first <;> cases second <;>
        simp [allEvents, v13BoolPairRepeatedStep,
          v13BoolPairSecondCoordinateStep, v13BoolPairDiagonalStep,
          V13SwitchedStep.successEvent] at hω ⊢

/-- The forced diagonal event cannot be the third conditional half-step after
the two coordinate-success cuts. -/
theorem not_prefixHalfStep_v13BoolPairDiagonalStep_after_firstSecond :
    ¬ PrefixHalfStep
      [v13BoolPairRepeatedStep.successEvent,
        v13BoolPairSecondCoordinateStep.successEvent]
      v13BoolPairDiagonalStep.successEvent := by
  exact
    not_prefixHalfStep_of_history_imp_event_of_positive
      (Ω := Bool × Bool)
      (hist :=
        [v13BoolPairRepeatedStep.successEvent,
          v13BoolPairSecondCoordinateStep.successEvent])
      (event := v13BoolPairDiagonalStep.successEvent)
      (by
        rw [v13BoolPairFirstSecond_success_count]
        decide)
      v13BoolPairFirstSecond_forcesDiagonal

/-- The second-coordinate step paired with the one-cell history field. -/
def v13BoolPairSecondCoordinateUnitFieldedStep :
    V13FieldedStep (Bool × Bool) where
  field := v13BoolPairUnitField
  step := v13BoolPairSecondCoordinateStep

/-- The diagonal step paired with the one-cell history field. -/
def v13BoolPairDiagonalUnitFieldedStep :
    V13FieldedStep (Bool × Bool) where
  field := v13BoolPairUnitField
  step := v13BoolPairDiagonalStep

/-- The one-cell field certifies the second-coordinate cut after
first-coordinate success. -/
theorem v13FieldPrefixInstantiation_secondCoordinateUnitField_after_first :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairSecondCoordinateStep := by
  refine v13FieldPrefixInstantiation_of_cellHalf ?_
  intro cell
  cases cell
  decide

/-- The first two one-cell fielded cuts are genuinely instantiable. -/
theorem v13BoolPairFirstSecondUnitFielded_instantiated :
    V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] := by
  refine ⟨v13FieldPrefixInstantiation_unitField_empty, ?_⟩
  simpa [v13BoolPairUnitFieldedStep,
    v13BoolPairSecondCoordinateUnitFieldedStep] using
    (⟨v13FieldPrefixInstantiation_secondCoordinateUnitField_after_first,
      trivial⟩ :
      V13FieldSwitchingInstantiatedFrom
        [v13BoolPairRepeatedStep.successEvent]
        [v13BoolPairSecondCoordinateUnitFieldedStep])

/-- The three-step Boolean-square list has a forced positive third fielded
step: after the two coordinate successes, diagonal success is automatic. -/
theorem v13BoolPairForcedDiagonalFieldedStepFrom :
    V13ForcedPositiveFieldedStepFrom
      ([] : List (FiniteEvent (Bool × Bool)))
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep,
        v13BoolPairDiagonalUnitFieldedStep] := by
  refine
    ⟨[v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep],
      v13BoolPairDiagonalUnitFieldedStep, [], rfl, ?_, ?_⟩
  · have hpos :
        0 < finiteHistoryCount (Bool × Bool)
          [v13BoolPairRepeatedStep.successEvent,
            v13BoolPairSecondCoordinateStep.successEvent] := by
      rw [v13BoolPairFirstSecond_success_count]
      decide
    simpa [v13FieldedSuccessEvents, v13BoolPairUnitFieldedStep,
      v13BoolPairSecondCoordinateUnitFieldedStep] using hpos
  · intro ω hω
    exact v13BoolPairFirstSecond_forcesDiagonal ω (by
      simpa [v13FieldedSuccessEvents, v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] using hω)

/-- The first two one-cell cuts instantiate, but adding the forced diagonal
third step blocks the fixed-field route. -/
theorem v13BoolPairFirstSecondThenForcedDiagonal_blocked :
    V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep,
          v13BoolPairSecondCoordinateUnitFieldedStep,
          v13BoolPairDiagonalUnitFieldedStep] := by
  exact
    ⟨v13BoolPairFirstSecondUnitFielded_instantiated,
      (v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute
        v13BoolPairForcedDiagonalFieldedStepFrom).1⟩

/-- The same forced diagonal example blocks the operational same-cell matching
formulation. -/
theorem not_v13FieldSwitchingFailureMatching_boolPair_forcedDiagonal :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep,
        v13BoolPairDiagonalUnitFieldedStep] := by
  exact
    (v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute
      v13BoolPairForcedDiagonalFieldedStepFrom).2

end BoolPairForcedDiagonal

end Mettapedia.Computability.PNP
