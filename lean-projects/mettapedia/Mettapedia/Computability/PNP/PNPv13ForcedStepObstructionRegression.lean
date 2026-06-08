import Mettapedia.Computability.PNP.PNPv13ForcedStepObstruction

/-!
# Regression checks for PNP v13 forced-step obstructions

These wrappers pin the distinction between literal repeated pivots and later
success events that are only logically forced by the accumulated positive
history.
-/

namespace Mettapedia.Computability.PNP.PNPv13ForcedStepObstructionRegression

open Mettapedia.Computability.PNP

universe u

theorem forced_positive_step_blocks_abstract_switching_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hforced : V13ForcedPositiveStepFrom hist steps) :
    ¬ V13SwitchingInstantiatedFrom hist steps := by
  exact not_v13SwitchingInstantiatedFrom_of_forcedPositiveStep hforced

theorem forced_positive_step_blocks_concrete_switching_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hforced : V13ForcedPositiveStepFrom hist steps) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist steps := by
  exact not_v13ConcreteSwitchingInstantiatedFrom_of_forcedPositiveStep hforced

theorem forced_positive_fielded_step_blocks_fixed_route_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hforced : V13ForcedPositiveFieldedStepFrom hist items) :
    (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute hforced

theorem bool_pair_first_second_force_diagonal_regression :
    ∀ ω, allEvents
      [v13BoolPairRepeatedStep.successEvent,
        v13BoolPairSecondCoordinateStep.successEvent] ω →
      v13BoolPairDiagonalStep.successEvent.pred ω := by
  exact v13BoolPairFirstSecond_forcesDiagonal

theorem bool_pair_forced_diagonal_not_prefix_half_step_regression :
    ¬ PrefixHalfStep
      [v13BoolPairRepeatedStep.successEvent,
        v13BoolPairSecondCoordinateStep.successEvent]
      v13BoolPairDiagonalStep.successEvent := by
  exact not_prefixHalfStep_v13BoolPairDiagonalStep_after_firstSecond

theorem bool_pair_first_two_unit_fields_valid_then_forced_third_blocked_regression :
    V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep,
          v13BoolPairSecondCoordinateUnitFieldedStep,
          v13BoolPairDiagonalUnitFieldedStep] := by
  exact v13BoolPairFirstSecondThenForcedDiagonal_blocked

theorem bool_pair_forced_diagonal_blocks_matching_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep,
        v13BoolPairDiagonalUnitFieldedStep] := by
  exact not_v13FieldSwitchingFailureMatching_boolPair_forcedDiagonal

end Mettapedia.Computability.PNP.PNPv13ForcedStepObstructionRegression
