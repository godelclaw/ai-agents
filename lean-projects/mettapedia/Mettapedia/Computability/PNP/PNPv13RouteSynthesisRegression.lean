import Mettapedia.Computability.PNP.PNPv13RouteSynthesis

/-!
# Regression checks for the PNP v13 switching route synthesis layer

These wrappers pin the decision-surface theorems used to audit the fixed-field
v13 product-success route.
-/

namespace Mettapedia.Computability.PNP.PNPv13RouteSynthesisRegression

open Mettapedia.Computability.PNP

universe u

theorem repeated_positive_pivot_blocks_abstract_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13SwitchedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13SwitchedStep Ω)}
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13SuccessEvents pre) ++ [step.successEvent])) :
    ¬ V13SwitchingInstantiatedFrom hist (pre ++ step :: step :: suffix) := by
  exact
    not_v13SwitchingInstantiatedFrom_repeatedPositivePivot_at
      (hist := hist) (pre := pre) (step := step) (suffix := suffix) hpos

theorem instantiated_abstract_route_has_no_repeated_positive_pivot_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    V13NoRepeatedPositivePivotFrom hist steps := by
  exact v13NoRepeatedPositivePivotFrom_of_v13SwitchingInstantiatedFrom h

theorem repeated_positive_fielded_pivot_blocks_route_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hrep : V13RepeatedPositiveFieldedPivotFrom hist items) :
    (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact v13RepeatedPositiveFieldedPivot_blocks_fixedFieldRoute hrep

theorem fielded_matching_has_no_repeated_positive_pivot_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hmatch : V13FieldSwitchingFailureMatchingFrom hist items) :
    V13NoRepeatedPositiveFieldedPivotFrom hist items := by
  exact v13NoRepeatedPositiveFieldedPivotFrom_of_failureMatchingFrom hmatch

theorem bad_cell_blocks_fixed_field_route_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad : V13FieldedBadCellFrom hist items) :
    (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad,
      not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hbad⟩

theorem fielded_matching_has_no_bad_cell_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hmatch : V13FieldSwitchingFailureMatchingFrom hist items) :
    V13NoFieldedBadCellFrom hist items := by
  exact v13NoFieldedBadCellFrom_of_failureMatchingFrom hmatch

theorem product_violation_yields_bad_cell_and_blocks_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    V13FieldedBadCellFrom hist items ∧
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact v13FieldedProductViolation_yields_badCell_and_blocks hbad

theorem fixed_field_route_obligations_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    V13NoRepeatedPositiveFieldedPivotFrom hist items ∧
      V13NoFieldedBadCellFrom hist items ∧
        2 ^ items.length *
            finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
          finiteHistoryCount Ω hist := by
  exact v13FieldedRouteObligations_of_v13FieldSwitchingInstantiatedFrom h

theorem bool_pair_repeated_one_cell_has_synthesis_bad_cell_regression :
    V13FieldedBadCellFrom
      ([] : List (FiniteEvent (Bool × Bool)))
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact
    v13FieldedBadCellFrom_of_product_bound_violation
      v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

theorem bool_pair_repeated_one_cell_blocks_fixed_field_route_regression :
    (¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep]) ∧
      ¬ V13FieldSwitchingFailureMatching
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  have hbad :
      V13FieldedBadCellFrom
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] :=
    bool_pair_repeated_one_cell_has_synthesis_bad_cell_regression
  exact
    ⟨by
      simpa [V13FieldSwitchingInstantiated] using
        not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad,
      by
        simpa [V13FieldSwitchingFailureMatching] using
          not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hbad⟩

end Mettapedia.Computability.PNP.PNPv13RouteSynthesisRegression
