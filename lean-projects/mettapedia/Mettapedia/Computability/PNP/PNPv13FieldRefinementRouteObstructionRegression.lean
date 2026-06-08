import Mettapedia.Computability.PNP.PNPv13FieldRefinementRouteObstruction

/-!
# Regression checks for the PNP v13 field-refinement route obstruction

These wrappers pin the strengthened refinement blocker that lifts a bad coarse
field cell all the way to the whole fielded switching route.
-/

namespace Mettapedia.Computability.PNP.PNPv13FieldRefinementRouteObstructionRegression

open Mettapedia.Computability.PNP

/-- The repeated first-coordinate step paired with the finer second-coordinate
field on the Boolean square. -/
def v13BoolPairSecondCoordinateRepeatedFieldedStep :
    V13FieldedStep (Bool × Bool) where
  field := v13BoolPairSecondCoordinateField
  step := v13BoolPairRepeatedStep

/-- The second-coordinate field is a genuine refinement of the one-cell field:
it splits the unique coarse cell into two finite fibers. -/
def v13BoolPairSecondCoordinateField_refines_unit :
    V13HistoryFieldRefinement
      v13BoolPairSecondCoordinateField v13BoolPairUnitField where
  project := fun _ => PUnit.unit
  cellOf_project := by
    intro ω
    rfl

theorem bool_pair_unit_then_secondCoordinateRepeatedField_has_refined_bad_cell_regression :
    V13FieldedBadCellFrom
      ([] : List (FiniteEvent (Bool × Bool)))
      [v13BoolPairUnitFieldedStep, v13BoolPairSecondCoordinateRepeatedFieldedStep] := by
  simpa [v13BoolPairSecondCoordinateRepeatedFieldedStep] using
    (v13FieldedBadCellFrom_append_cons_of_refinement_bad_coarse_cell
      (Ω := Bool × Bool)
      (fine := v13BoolPairSecondCoordinateField)
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairUnitFieldedStep)
      (suffix := [])
      (coarseCell := PUnit.unit)
      v13BoolPairSecondCoordinateField_refines_unit
      v13BoolPairUnitField_repeatedSuccess_bad_cell)

theorem bool_pair_unit_then_secondCoordinateRepeatedField_refinement_blocks_route_regression :
    (¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairSecondCoordinateRepeatedFieldedStep]) ∧
      ¬ V13FieldSwitchingFailureMatching
        [v13BoolPairUnitFieldedStep, v13BoolPairSecondCoordinateRepeatedFieldedStep] := by
  simpa [V13FieldSwitchingInstantiated, V13FieldSwitchingFailureMatching,
    v13BoolPairSecondCoordinateRepeatedFieldedStep] using
    (v13FieldRefinementBadCoarseCell_blocks_fixedFieldRoute_at
      (Ω := Bool × Bool)
      (fine := v13BoolPairSecondCoordinateField)
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairUnitFieldedStep)
      (suffix := [])
      (coarseCell := PUnit.unit)
      v13BoolPairSecondCoordinateField_refines_unit
      v13BoolPairUnitField_repeatedSuccess_bad_cell)

end Mettapedia.Computability.PNP.PNPv13FieldRefinementRouteObstructionRegression
