import Mettapedia.Computability.PNP.PNPv13RouteSynthesis

/-!
# PNP v13 fixed-field refinement

This file records a small but important guardrail for the fixed-field route:
refining a supplied history field cannot hide a bad coarse cell.  If a coarse
cell has strictly more next-success points than next-failure points, then any
genuine finite refinement of that field has a refined cell with the same
strict imbalance.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- A finite history field `fine` refines a field `coarse` when every fine cell
has a canonical image coarse cell and the pointwise cell maps commute. -/
structure V13HistoryFieldRefinement {Ω : Type u}
    (fine coarse : V13HistoryField Ω) where
  project : fine.Cell → coarse.Cell
  cellOf_project : ∀ ω : Ω, project (fine.cellOf ω) = coarse.cellOf ω

/-- A finite event count is zero when the event is pointwise impossible. -/
theorem finiteEventCount_eq_zero_of_forall_not
    {Ω : Type u} [Fintype Ω]
    {E : Ω → Prop} [DecidablePred E]
    (hnone : ∀ ω, ¬ E ω) :
    finiteEventCount Ω E = 0 := by
  simp [finiteEventCount, hnone]

/-- Under a field refinement, a coarse success count is the sum of the refined
success counts over fine cells that project to the coarse cell. -/
theorem v13ConcreteSuccessCount_eq_sum_refinedCells
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (coarseCell : coarse.Cell) :
    v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell =
      Finset.univ.sum (fun fineCell =>
        if refn.project fineCell = coarseCell then
          v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell
        else 0) := by
  rw [v13ConcreteSuccessCount]
  have hpartition :=
    finiteEventCount_cell_partition (Ω := Ω) (Cell := fine.Cell)
      (E := fun ω =>
        allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          step.successEvent.pred ω)
      fine.cellOf
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro fineCell _hfineCell
  by_cases hcell : refn.project fineCell = coarseCell
  · simp [hcell, v13ConcreteSuccessCount]
    exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          step.successEvent.pred ω) ∧ fine.cellOf ω = fineCell)
      (F := fun ω =>
        allEvents hist ω ∧ fine.cellOf ω = fineCell ∧
          step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2.2⟩
        · intro h
          refine ⟨⟨h.1, ?_, h.2.2⟩, h.2.1⟩
          calc
            coarse.cellOf ω = refn.project (fine.cellOf ω) :=
              (refn.cellOf_project ω).symm
            _ = refn.project fineCell := by rw [h.2.1]
            _ = coarseCell := hcell)
  · simp [hcell]
    exact finiteEventCount_eq_zero_of_forall_not (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          step.successEvent.pred ω) ∧ fine.cellOf ω = fineCell)
      (by
        intro ω h
        exact hcell (by
          calc
            refn.project fineCell = refn.project (fine.cellOf ω) := by
              rw [h.2]
            _ = coarse.cellOf ω := refn.cellOf_project ω
            _ = coarseCell := h.1.2.1))

/-- Under a field refinement, a coarse failure count is the sum of the refined
failure counts over fine cells that project to the coarse cell. -/
theorem v13ConcreteFailureCount_eq_sum_refinedCells
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (coarseCell : coarse.Cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell =
      Finset.univ.sum (fun fineCell =>
        if refn.project fineCell = coarseCell then
          v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell
        else 0) := by
  rw [v13ConcreteFailureCount]
  have hpartition :=
    finiteEventCount_cell_partition (Ω := Ω) (Cell := fine.Cell)
      (E := fun ω =>
        allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          ¬ step.successEvent.pred ω)
      fine.cellOf
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro fineCell _hfineCell
  by_cases hcell : refn.project fineCell = coarseCell
  · simp [hcell, v13ConcreteFailureCount]
    exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          ¬ step.successEvent.pred ω) ∧ fine.cellOf ω = fineCell)
      (F := fun ω =>
        allEvents hist ω ∧ fine.cellOf ω = fineCell ∧
          ¬ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2.2⟩
        · intro h
          refine ⟨⟨h.1, ?_, h.2.2⟩, h.2.1⟩
          calc
            coarse.cellOf ω = refn.project (fine.cellOf ω) :=
              (refn.cellOf_project ω).symm
            _ = refn.project fineCell := by rw [h.2.1]
            _ = coarseCell := hcell)
  · simp [hcell]
    exact finiteEventCount_eq_zero_of_forall_not (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ coarse.cellOf ω = coarseCell ∧
          ¬ step.successEvent.pred ω) ∧ fine.cellOf ω = fineCell)
      (by
        intro ω h
        exact hcell (by
          calc
            refn.project fineCell = refn.project (fine.cellOf ω) := by
              rw [h.2]
            _ = coarse.cellOf ω := refn.cellOf_project ω
            _ = coarseCell := h.1.2.1))

/-- A bad coarse cell remains visible in every finite refinement: some refined
cell lying over it still has strictly fewer failures than successes. -/
theorem exists_refined_bad_cell_of_bad_coarse_cell
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
  by_contra hno
  have hterm :
      ∀ fineCell : fine.Cell,
        (if refn.project fineCell = coarseCell then
          v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell
        else 0) ≤
        (if refn.project fineCell = coarseCell then
          v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell
        else 0) := by
    intro fineCell
    by_cases hcell : refn.project fineCell = coarseCell
    · simp [hcell]
      exact le_of_not_gt (by
        intro hbadFine
        exact hno ⟨fineCell, hcell, hbadFine⟩)
    · simp [hcell]
  have hsum :
      Finset.univ.sum (fun fineCell =>
        if refn.project fineCell = coarseCell then
          v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell
        else 0) ≤
        Finset.univ.sum (fun fineCell =>
          if refn.project fineCell = coarseCell then
            v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell
          else 0) :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun fineCell _hmem => hterm fineCell)
  have hsuccess :=
    v13ConcreteSuccessCount_eq_sum_refinedCells
      (Ω := Ω) refn hist step coarseCell
  have hfailure :=
    v13ConcreteFailureCount_eq_sum_refinedCells
      (Ω := Ω) refn hist step coarseCell
  have hle :
      v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell ≤
        v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell := by
    simpa [hsuccess, hfailure] using hsum
  exact (not_lt_of_ge hle) hbad

/-- Consequently, if a coarse field has a bad cell, no refinement of that field
can supply a fixed-field prefix certificate for the same history and step. -/
theorem not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {coarseCell : coarse.Cell}
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell) :
    ¬ V13FieldPrefixInstantiation fine hist step := by
  rcases exists_refined_bad_cell_of_bad_coarse_cell
      (Ω := Ω) refn hbad with
    ⟨fineCell, _hcell, hbadFine⟩
  exact not_v13FieldPrefixInstantiation_of_success_gt_failure fineCell hbadFine

end Mettapedia.Computability.PNP
