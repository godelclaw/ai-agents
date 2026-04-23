import Mettapedia.Computability.PNP.PNPv13FieldRefinement

/-!
# Regression checks for PNP v13 fixed-field refinement

These wrappers pin the theorem that field refinement preserves bad-cell
obstructions.
-/

namespace Mettapedia.Computability.PNP.PNPv13FieldRefinementRegression

open Mettapedia.Computability.PNP

universe u

theorem bad_coarse_cell_has_bad_refined_cell_regression
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {coarseCell : coarse.Cell}
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell) :
    ∃ fineCell : fine.Cell,
      refn.project fineCell = coarseCell ∧
        v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell <
          v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell := by
  exact exists_refined_bad_cell_of_bad_coarse_cell refn hbad

theorem refined_bad_coarse_cell_blocks_prefix_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {coarseCell : coarse.Cell}
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell) :
    ¬ V13FieldPrefixInstantiation fine hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell refn hbad

theorem bool_pair_unit_field_bad_cell_survives_refinement_regression
    {fine : V13HistoryField (Bool × Bool)}
    (refn : V13HistoryFieldRefinement fine v13BoolPairUnitField) :
    ∃ fineCell : fine.Cell,
      refn.project fineCell = PUnit.unit ∧
        v13ConcreteFailureCount (Ω := Bool × Bool)
            [v13BoolPairRepeatedStep.successEvent]
            v13BoolPairRepeatedStep fine.cellOf fineCell <
          v13ConcreteSuccessCount (Ω := Bool × Bool)
            [v13BoolPairRepeatedStep.successEvent]
            v13BoolPairRepeatedStep fine.cellOf fineCell := by
  exact
    exists_refined_bad_cell_of_bad_coarse_cell refn
      v13BoolPairUnitField_repeatedSuccess_bad_cell

theorem bool_pair_unit_field_refinement_blocks_second_prefix_regression
    {fine : V13HistoryField (Bool × Bool)}
    (refn : V13HistoryFieldRefinement fine v13BoolPairUnitField) :
    ¬ V13FieldPrefixInstantiation fine
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell refn
      v13BoolPairUnitField_repeatedSuccess_bad_cell

end Mettapedia.Computability.PNP.PNPv13FieldRefinementRegression
