import Mettapedia.Computability.PNP.PNPv13FieldRefinementFailedPrefixObstruction
import Mettapedia.Computability.PNP.PNPv13ForcedStepObstruction

/-!
# Regression checks for refined failed-prefix obstructions

These checks pin the abstract failure-monotonicity theorem on the same
Boolean-square refinement witness used in the earlier refinement files, but
with the premise reduced to the genuinely minimal route-facing statement:
the coarse prefix already fails.
-/

namespace Mettapedia.Computability.PNP.PNPv13FieldRefinementFailedPrefixObstructionRegression

open Mettapedia.Computability.PNP

/-- The identity field on the Boolean square. -/
def v13BoolPairIdentityField : V13HistoryField (Bool × Bool) where
  Cell := Bool × Bool
  cellOf := fun ω => ω

/-- The repeated first-coordinate step paired with the identity field. -/
def v13BoolPairIdentityRepeatedFieldedStep : V13FieldedStep (Bool × Bool) where
  field := v13BoolPairIdentityField
  step := v13BoolPairRepeatedStep

/-- The identity field genuinely refines the second-coordinate field by
forgetting the first coordinate. -/
def v13BoolPairIdentityField_refines_secondCoordinate :
    V13HistoryFieldRefinement
      v13BoolPairIdentityField v13BoolPairSecondCoordinateField where
  project := fun ω => ω.2
  cellOf_project := by
    intro ω
    rfl

theorem not_v13FieldPrefixInstantiation_identityField_diagonal_repeated_of_failedCoarsePrefix_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairIdentityField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_refinement_not_fieldPrefixInstantiation
      v13BoolPairIdentityField_refines_secondCoordinate
      not_v13FieldPrefixInstantiation_secondCoordinateField_diagonal_by_determines_success_on

theorem v13FieldPrefixInstantiation_diagonalUnitField_empty_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairDiagonalStep := by
  refine v13FieldPrefixInstantiation_of_cellHalf ?_
  intro cell
  cases cell
  decide

theorem v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonalStep_regression :
    V13HistoryFieldDeterminesSuccessOn v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalStep.successEvent] v13BoolPairRepeatedStep := by
  intro ω ω' hω hω' hcell hsucc
  have hωDiag : allEvents [v13BoolPairDiagonalEvent] ω := by
    simpa [allEvents, v13BoolPairDiagonalEvent, v13BoolPairDiagonalStep,
      V13SwitchedStep.successEvent] using hω
  have hω'Diag : allEvents [v13BoolPairDiagonalEvent] ω' := by
    simpa [allEvents, v13BoolPairDiagonalEvent, v13BoolPairDiagonalStep,
      V13SwitchedStep.successEvent] using hω'
  exact
    v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal
      hωDiag hω'Diag hcell hsucc

theorem not_v13FieldPrefixInstantiation_secondCoordinateField_after_diagonalStep_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      (([] : List (FiniteEvent (Bool × Bool))) ++
        v13FieldedSuccessEvents [v13BoolPairDiagonalUnitFieldedStep])
      v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonalStep_regression
      (by
        decide :
          0 < finiteHistoryCount (Bool × Bool)
            ([v13BoolPairDiagonalStep.successEvent] ++
              [v13BoolPairRepeatedStep.successEvent]))

theorem bool_pair_diagonal_then_identityRepeated_refinement_failedPrefix_blocks_route_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairDiagonalStep ∧
      (¬ V13FieldSwitchingInstantiatedFrom
          ([] : List (FiniteEvent (Bool × Bool)))
          [v13BoolPairDiagonalUnitFieldedStep,
            v13BoolPairIdentityRepeatedFieldedStep]) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom
          ([] : List (FiniteEvent (Bool × Bool)))
          [v13BoolPairDiagonalUnitFieldedStep,
            v13BoolPairIdentityRepeatedFieldedStep] := by
  have hblock :=
    v13FieldRefinementFailedPrefix_blocks_fixedFieldRoute_at
      (Ω := Bool × Bool)
      (fine := v13BoolPairIdentityField)
      (coarse := v13BoolPairSecondCoordinateField)
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairDiagonalUnitFieldedStep])
      (step := v13BoolPairRepeatedStep)
      (suffix := [])
      v13BoolPairIdentityField_refines_secondCoordinate
      not_v13FieldPrefixInstantiation_secondCoordinateField_after_diagonalStep_regression
  exact ⟨v13FieldPrefixInstantiation_diagonalUnitField_empty_regression, hblock.1, hblock.2⟩

end Mettapedia.Computability.PNP.PNPv13FieldRefinementFailedPrefixObstructionRegression
