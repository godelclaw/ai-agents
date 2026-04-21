import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiation

/-!
# Regression checks for the PNP v13 switching instantiation interface

These wrappers pin the v13-specific bridge from finite history-cell ledgers to
the generic tower-product theorem.
-/

namespace Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression

open Mettapedia.Computability.PNP

universe u

theorem prefix_half_step_from_v13_prefix_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13PrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiation cert

def v13_prefix_certificate_from_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13PrefixInstantiation hist step := by
  exact v13PrefixInstantiation_of_prefixHalfStep h

theorem v13_prefix_instantiated_iff_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13PrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  exact v13PrefixInstantiated_iff_prefixHalfStep

theorem no_v13_prefix_certificate_from_failed_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13PrefixInstantiated hist step := by
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep hfail

def v13_prefix_certificate_from_concrete_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    V13PrefixInstantiation hist step := by
  exact v13PrefixInstantiation_of_concretePrefixInstantiation cert

theorem prefix_half_step_from_concrete_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13ConcretePrefixInstantiation cert

theorem finite_event_count_cell_partition_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {E : Ω → Prop} [DecidablePred E] (cellOf : Ω → Cell) :
    finiteEventCount Ω E =
      Finset.univ.sum (fun cell =>
        finiteEventCount Ω (fun ω => E ω ∧ cellOf ω = cell)) := by
  exact finiteEventCount_cell_partition cellOf

theorem finite_event_count_split_regression
    {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F] :
    finiteEventCount Ω E =
      finiteEventCount Ω (fun ω => E ω ∧ F ω) +
        finiteEventCount Ω (fun ω => E ω ∧ ¬ F ω) := by
  exact finiteEventCount_split

theorem concrete_prefix_count_decomp_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (cellOf : Ω → Cell) :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf) := by
  exact v13ConcretePrefixCount_decomp hist cellOf

theorem concrete_success_count_decomp_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
  exact v13ConcreteSuccessCount_decomp hist step cellOf

theorem concrete_prefix_count_success_failure_split_regression
    {Ω Cell : Type u} [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    v13ConcretePrefixCount (Ω := Ω) hist cellOf cell =
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell +
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  exact v13ConcretePrefixCount_eq_success_add_failure hist step cellOf cell

theorem concrete_cell_half_iff_success_le_failure_regression
    {Ω Cell : Type u} [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    (2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) ↔
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  exact v13ConcreteCellHalf_iff_success_le_failure hist step cellOf cell

def concrete_prefix_certificate_from_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_prefixHalfStep h

def concrete_prefix_certificate_from_cell_half_regression
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cellOf : Ω → Cell)
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_cellHalf cellOf hhalf

theorem concrete_prefix_instantiated_iff_prefix_half_step_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13ConcretePrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  exact v13ConcretePrefixInstantiated_iff_prefixHalfStep

def concrete_prefix_certificate_from_field_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    V13ConcretePrefixInstantiation hist step := by
  exact v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation cert

theorem prefix_half_step_from_field_certificate_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13FieldPrefixInstantiation cert

def field_prefix_certificate_from_cell_half_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    V13FieldPrefixInstantiation field hist step := by
  exact v13FieldPrefixInstantiation_of_cellHalf hhalf

theorem field_prefix_certificate_iff_cell_half_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact v13FieldPrefixInstantiation_iff_cellHalf

theorem field_prefix_certificate_iff_success_le_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  exact v13FieldPrefixInstantiation_iff_success_le_failure

theorem field_failure_matching_iff_success_le_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldFailureMatching field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  exact v13FieldFailureMatching_iff_success_le_failure

theorem field_prefix_certificate_iff_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      V13FieldFailureMatching field hist step := by
  exact v13FieldPrefixInstantiation_iff_failureMatching

def field_prefix_certificate_from_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step) :
    V13FieldPrefixInstantiation field hist step :=
  v13FieldPrefixInstantiation_of_failureMatching hmatch

theorem same_cell_failure_from_failure_matching_success_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      hmatch hhist hsucc

theorem no_failure_matching_from_success_without_same_cell_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem same_cell_failure_from_field_certificate_success_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldPrefixInstantiation_success
      cert hhist hsucc

theorem no_field_prefix_certificate_from_no_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_not_failureMatching hfail

theorem no_field_prefix_certificate_from_success_without_same_cell_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem no_failure_matching_from_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem failure_matching_blocks_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess field step := by
  exact
    not_v13HistoryFieldDeterminesSuccess_of_failureMatching_positive_success
      hmatch hpos

theorem field_determines_success_on_from_global_regression
    {Ω : Type u}
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step) :
    V13HistoryFieldDeterminesSuccessOn field hist step := by
  exact v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet

theorem no_failure_matching_from_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem failure_matching_blocks_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn field hist step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      hmatch hpos

theorem no_field_prefix_certificate_from_success_gt_failure_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_success_gt_failure cell hbad

theorem field_determines_success_failure_count_zero_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccess_of_success_pos
      hdet cell hpos

theorem field_determines_success_on_failure_count_zero_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_cell_success
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_on_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
      hdet cell hpos

theorem no_field_prefix_certificate_from_determined_success_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem no_field_prefix_certificate_from_determined_success_on_positive_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem no_field_prefix_certificate_from_bad_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hbad :
      ¬ 2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation cell hbad

theorem success_history_field_determines_success_regression
    {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13HistoryFieldDeterminesSuccess (v13SuccessHistoryField step) step := by
  exact v13SuccessHistoryField_determinesSuccess step

theorem success_history_field_true_cell_count_regression
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      finiteHistoryCount Ω (hist ++ [step.successEvent]) := by
  exact v13SuccessHistoryField_prefix_true_count hist step

theorem field_certificate_success_cell_is_mixed_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact
    v13FieldPrefixInstantiation_successCount_lt_prefixCount_of_success_pos
      cert cell hpos

theorem field_certificate_one_success_requires_two_prefix_points_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hsucc :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    2 ≤ v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  exact
    v13FieldPrefixInstantiation_two_le_prefixCount_of_successCount_eq_one
      cert cell hsucc

theorem no_field_prefix_certificate_from_total_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hpos :
      0 < v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix cell hpos hall

theorem no_field_prefix_certificate_from_positive_total_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix
      cell hpos hall

theorem no_field_prefix_certificate_from_singleton_success_cell_regression
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cell : field.Cell)
    (hprefix :
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell = 1)
    (hsuccess :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_singleton_success_cell
      cell hprefix hsuccess

theorem no_success_history_field_certificate_from_positive_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation (v13SuccessHistoryField step) hist step := by
  exact
    not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success hpos

theorem sequential_half_from_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) := by
  exact sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom h

theorem product_bound_from_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiated items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_fieldInstantiated items h

theorem field_instantiation_iff_cell_half_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingCellHalfFrom hist items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom

theorem field_instantiation_empty_iff_cell_half_regression
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingCellHalf items := by
  exact v13FieldSwitchingInstantiated_iff_cellHalf

theorem field_instantiation_iff_failure_matching_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingFailureMatchingFrom hist items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom

theorem field_instantiation_empty_iff_failure_matching_regression
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingFailureMatching items := by
  exact v13FieldSwitchingInstantiated_iff_failureMatching

theorem product_bound_from_field_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatching items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_fieldFailureMatching items h

theorem product_bound_violation_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingInstantiated items := by
  exact not_v13FieldSwitchingInstantiated_of_product_bound_violation hbad

theorem product_bound_violation_blocks_field_failure_matching_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_of_product_bound_violation hbad

theorem product_bound_violation_blocks_field_failure_matching_regression
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingFailureMatching items := by
  exact not_v13FieldSwitchingFailureMatching_of_product_bound_violation hbad

theorem failed_field_failure_matching_position_from_not_matching_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_not_failureMatchingFrom
      hfail

theorem failed_field_failure_matching_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_product_bound_violation
      hbad

theorem failed_field_prefix_position_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ∃ pre item suffix,
      items = pre ++ item :: suffix ∧
        ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldPrefixInstantiation_at_append_cons_of_product_bound_violation
      hbad

theorem failed_field_prefix_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {item : V13FieldedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldPrefixInstantiation item.field hist item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      hfail

theorem failed_failure_matching_blocks_field_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  exact not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom hfail

theorem extract_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix)) :
    V13FieldFailureMatching item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom hmatch

theorem same_cell_failure_after_prefix_from_matching_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents (hist ++ v13FieldedSuccessEvents pre) ω' ∧
        item.field.cellOf ω' = item.field.cellOf ω ∧
          ¬ item.step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
      hmatch hhist hsucc

theorem success_without_same_cell_failure_blocks_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem failure_matching_after_prefix_blocks_determined_success_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess item.field item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccess_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos

theorem failure_matching_after_prefix_blocks_determined_success_on_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos

theorem determined_success_field_blocks_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_failure_matching_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem determined_success_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccessOn item.field hist item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem failed_field_prefix_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hfail :
      ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      hfail

theorem success_without_same_cell_failure_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_success_without_sameCell_failure
      hhist hsucc hnoFailure

theorem determined_success_field_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      hdet hpos

theorem determined_success_on_field_blocks_field_instantiation_after_prefix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos

theorem success_revealing_field_blocks_field_suffix_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (v13SuccessFieldedStep step :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
      hpos

theorem sequential_half_from_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom h

theorem v13_instantiation_from_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13SwitchingInstantiatedFrom hist steps := by
  exact v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom h

theorem v13_instantiation_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

theorem v13_instantiation_empty_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiated_iff_sequentialHalfAdmissible

theorem v13_instantiation_from_concrete_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    V13SwitchingInstantiatedFrom hist steps := by
  exact v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h

theorem concrete_v13_instantiation_from_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13ConcreteSwitchingInstantiatedFrom hist steps := by
  exact v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom h

theorem concrete_v13_instantiation_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

theorem concrete_v13_instantiation_empty_iff_sequential_half_regression
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiated_iff_sequentialHalfAdmissible

theorem product_bound_from_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_instantiated steps h

theorem product_bound_from_concrete_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact v13_product_bound_of_concreteInstantiated steps h

theorem product_bound_violation_blocks_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13SwitchingInstantiated steps := by
  exact not_v13SwitchingInstantiated_of_product_bound_violation hbad

theorem product_bound_violation_blocks_concrete_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13ConcreteSwitchingInstantiated steps := by
  exact not_v13ConcreteSwitchingInstantiated_of_product_bound_violation hbad

theorem failed_prefix_blocks_v13_instantiation_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13SwitchedStep Ω)}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13SwitchingInstantiatedFrom hist (step :: rest) := by
  exact not_v13SwitchingInstantiatedFrom_cons_of_not_prefixHalfStep hfail

theorem first_step_global_half_regression :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairRepeatedStep.successEvent := by
  exact prefixHalfStep_v13BoolPairRepeatedStep_empty

theorem unit_field_first_step_certificate_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact v13FieldPrefixInstantiation_unitField_empty

theorem unit_field_first_step_failure_matching_regression :
    V13FieldFailureMatching v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    v13FieldPrefixInstantiation_iff_failureMatching.mp
      v13FieldPrefixInstantiation_unitField_empty

theorem first_coordinate_field_prefix_true_count_regression :
    v13ConcretePrefixCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  exact v13BoolPairFirstCoordinateField_prefix_true_count

theorem first_coordinate_field_success_true_count_regression :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  exact v13BoolPairFirstCoordinateField_success_true_count

theorem first_coordinate_field_failure_true_count_regression :
    v13ConcreteFailureCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 0 := by
  decide

theorem first_coordinate_field_determines_success_regression :
    V13HistoryFieldDeterminesSuccess v13BoolPairFirstCoordinateField
      v13BoolPairRepeatedStep := by
  exact v13BoolPairFirstCoordinateField_determinesSuccess

theorem second_coordinate_field_not_globally_determines_success_regression :
    ¬ V13HistoryFieldDeterminesSuccess v13BoolPairSecondCoordinateField
      v13BoolPairRepeatedStep := by
  exact not_v13BoolPairSecondCoordinateField_determinesSuccess

theorem second_coordinate_field_determines_success_on_diagonal_regression :
    V13HistoryFieldDeterminesSuccessOn v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal

theorem diagonal_repeated_step_success_count_regression :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairDiagonalEvent] ++ [v13BoolPairRepeatedStep.successEvent]) = 1 := by
  exact v13BoolPairDiagonal_repeatedStep_success_count

theorem second_coordinate_diagonal_true_cell_has_no_failure_regression :
    ∀ ⦃ω' : Bool × Bool⦄,
      allEvents [v13BoolPairDiagonalEvent] ω' →
        v13BoolPairSecondCoordinateField.cellOf ω' =
          v13BoolPairSecondCoordinateField.cellOf (true, true) →
            v13BoolPairRepeatedStep.successEvent.pred ω' := by
  intro ω' hhist hcell
  cases ω' with
  | mk a b =>
      cases a <;> cases b <;>
        simp [allEvents, v13BoolPairDiagonalEvent,
          v13BoolPairSecondCoordinateField, v13BoolPairRepeatedStep,
          V13SwitchedStep.successEvent] at hhist hcell ⊢

theorem no_fixed_first_coordinate_field_certificate_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_firstCoordinateField_empty

theorem no_fixed_first_coordinate_field_certificate_by_determined_success_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_firstCoordinateField_empty_by_determined_success

theorem no_second_coordinate_field_certificate_on_diagonal_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_secondCoordinateField_diagonal_by_determines_success_on

theorem no_second_coordinate_field_certificate_on_diagonal_by_pointwise_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
      (field := v13BoolPairSecondCoordinateField)
      (hist := [v13BoolPairDiagonalEvent])
      (step := v13BoolPairRepeatedStep)
      (ω := (true, true))
      (by
        simp [allEvents, v13BoolPairDiagonalEvent])
      (by
        decide)
      second_coordinate_diagonal_true_cell_has_no_failure_regression

theorem no_second_coordinate_failure_matching_on_diagonal_regression :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_secondCoordinateField_diagonal_by_determines_success_on

theorem no_second_coordinate_failure_matching_on_diagonal_by_pointwise_regression :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_of_success_without_sameCell_failure
      (field := v13BoolPairSecondCoordinateField)
      (hist := [v13BoolPairDiagonalEvent])
      (step := v13BoolPairRepeatedStep)
      (ω := (true, true))
      (by
        simp [allEvents, v13BoolPairDiagonalEvent])
      (by
        decide)
      second_coordinate_diagonal_true_cell_has_no_failure_regression

theorem no_first_coordinate_field_failure_matching_regression :
    ¬ V13FieldFailureMatching v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  intro hmatch
  exact not_v13FieldPrefixInstantiation_firstCoordinateField_empty
    (v13FieldPrefixInstantiation_of_failureMatching hmatch)

theorem prefix_half_without_fixed_first_coordinate_certificate_regression :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
        v13BoolPairRepeatedStep.successEvent ∧
      ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact prefixHalfStep_without_firstCoordinateFieldInstantiation

theorem no_field_instantiation_for_first_coordinate_one_step_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairFirstCoordinateFieldedStep] := by
  exact not_v13FieldSwitchingInstantiated_firstCoordinateOneStep

theorem unit_field_then_first_coordinate_field_second_blocked_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  exact unitField_first_step_then_firstCoordinateField_second_blocked

theorem no_failure_matching_for_unit_then_first_coordinate_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  intro hmatch
  exact unitField_first_step_then_firstCoordinateField_second_blocked.2
    (v13FieldSwitchingInstantiated_iff_failureMatching.mpr hmatch)

theorem no_failure_matching_for_unit_then_first_coordinate_by_determined_success_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairFirstCoordinateFieldedStep)
      (suffix := [])
      v13BoolPairFirstCoordinateField_determinesSuccess
      (by
        decide)

theorem no_success_revealing_field_certificate_bool_pair_regression :
    ¬ V13FieldPrefixInstantiation
      (v13SuccessHistoryField v13BoolPairRepeatedStep)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success
      (by
        decide)

theorem no_success_revealing_fielded_step_bool_pair_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13SuccessFieldedStep v13BoolPairRepeatedStep] := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
      (by
        decide)

theorem repeated_step_second_prefix_count_regression :
    finiteHistoryCount (Bool × Bool) [v13BoolPairRepeatedStep.successEvent] = 2 := by
  exact v13BoolPairRepeatedStep_success_count

theorem repeated_step_second_prefix_fails_regression :
    ¬ PrefixHalfStep [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep.successEvent := by
  exact not_prefixHalfStep_v13BoolPairRepeatedStep_after_success

theorem no_v13_certificate_for_repeated_second_step_regression :
    ¬ V13PrefixInstantiated [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep := by
  exact not_v13PrefixInstantiated_boolPairRepeatedStep_second

theorem repeated_two_steps_product_bound_violation_regression :
    ¬ 2 ^ [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13SuccessEvents
            [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  exact v13BoolPairRepeatedTwoSteps_product_bound_violation

theorem unit_field_repeated_two_steps_product_bound_violation_regression :
    ¬ 2 ^ [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13FieldedSuccessEvents
            [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  exact v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

theorem no_v13_instantiation_for_repeated_two_steps_regression :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps

theorem no_v13_instantiation_for_repeated_two_steps_by_product_bound_regression :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound

theorem unit_field_repeated_success_cell_has_no_failure_regression :
    ∀ ⦃ω' : Bool × Bool⦄,
      allEvents [v13BoolPairRepeatedStep.successEvent] ω' →
        v13BoolPairUnitField.cellOf ω' =
          v13BoolPairUnitField.cellOf (true, true) →
            v13BoolPairRepeatedStep.successEvent.pred ω' := by
  exact v13BoolPairUnitField_repeatedSuccess_cell_has_no_failure

theorem no_unit_field_failure_matching_after_repeated_success_regression :
    ¬ V13FieldFailureMatching v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact not_v13FieldFailureMatching_unitField_after_repeatedSuccess

theorem no_unit_field_prefix_certificate_after_repeated_success_regression :
    ¬ V13FieldPrefixInstantiation v13BoolPairUnitField
      [v13BoolPairRepeatedStep.successEvent] v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_unitField_after_repeatedSuccess

theorem unit_field_repeated_two_steps_second_step_blocked_regression :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact unitField_repeatedTwoSteps_second_step_blocked

theorem no_concrete_v13_instantiation_for_repeated_two_steps_by_product_bound_regression :
    ¬ V13ConcreteSwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact
    not_v13ConcreteSwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound

theorem no_field_instantiation_for_unit_field_repeated_two_steps_by_product_bound_regression :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact
    not_v13FieldSwitchingInstantiated_unitField_repeatedTwoSteps_by_product_bound

theorem no_failure_matching_for_unit_field_repeated_two_steps_by_product_bound_regression :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact
    not_v13FieldSwitchingFailureMatching_unitField_repeatedTwoSteps_by_product_bound

theorem failed_matching_position_for_unit_field_repeated_two_steps_regression :
    ∃ pre item suffix,
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] =
        pre ++ item :: suffix ∧
        ¬ V13FieldFailureMatching item.field
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldFailureMatching_at_append_cons_of_product_bound_violation
      v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

theorem failed_prefix_position_for_unit_field_repeated_two_steps_regression :
    ∃ pre item suffix,
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] =
        pre ++ item :: suffix ∧
        ¬ V13FieldPrefixInstantiation item.field
          (([] : List (FiniteEvent (Bool × Bool))) ++
            v13FieldedSuccessEvents pre) item.step := by
  exact
    exists_failed_fieldPrefixInstantiation_at_append_cons_of_product_bound_violation
      v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

end Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationRegression
