import Mettapedia.Computability.PNP.PNPv13FieldRefinement

/-!
# PNP v13 field-refinement route obstruction

Refining a bad fixed-history field cell cannot rescue the whole fielded
switching route.  Once a coarse field has a localized bad cell after an
explicit fielded prefix, every genuine refinement of that field still yields a
localized bad cell at the same position, so both the fixed-field certificate
route and the equivalent same-cell matching route fail for the refined suffix.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- Replacing the fixed field at one explicit fielded position by any genuine
refinement cannot remove a bad coarse cell at that position.  The refined list
still has a localized bad cell after the same preceding fielded prefix. -/
theorem v13FieldedBadCellFrom_append_cons_of_refinement_bad_coarse_cell
    {Ω : Type u} [Fintype Ω]
    {fine : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {coarseCell : item.field.Cell}
    (refn : V13HistoryFieldRefinement fine item.field)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω)
          (hist ++ v13FieldedSuccessEvents pre)
          item.step item.field.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω)
          (hist ++ v13FieldedSuccessEvents pre)
          item.step item.field.cellOf coarseCell) :
    V13FieldedBadCellFrom hist
      (pre ++ ({ field := fine, step := item.step } : V13FieldedStep Ω) :: suffix) := by
  rcases exists_refined_bad_cell_of_bad_coarse_cell
      (Ω := Ω) refn hbad with
    ⟨fineCell, _hproject, hbadFine⟩
  refine
    ⟨pre, ({ field := fine, step := item.step } : V13FieldedStep Ω), suffix,
      rfl, fineCell, ?_⟩
  simpa using hbadFine

/-- Therefore a bad coarse cell blocks the whole refined fielded suffix, both
as a fixed-field certificate list and as the equivalent same-cell matching
list. -/
theorem v13FieldRefinementBadCoarseCell_blocks_fixedFieldRoute_at
    {Ω : Type u} [Fintype Ω]
    {fine : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    {coarseCell : item.field.Cell}
    (refn : V13HistoryFieldRefinement fine item.field)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω)
          (hist ++ v13FieldedSuccessEvents pre)
          item.step item.field.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω)
          (hist ++ v13FieldedSuccessEvents pre)
          item.step item.field.cellOf coarseCell) :
    (¬ V13FieldSwitchingInstantiatedFrom hist
        (pre ++ ({ field := fine, step := item.step } : V13FieldedStep Ω) :: suffix)) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist
        (pre ++ ({ field := fine, step := item.step } : V13FieldedStep Ω) :: suffix) := by
  have hfieldedBad :
      V13FieldedBadCellFrom hist
        (pre ++ ({ field := fine, step := item.step } : V13FieldedStep Ω) :: suffix) :=
    v13FieldedBadCellFrom_append_cons_of_refinement_bad_coarse_cell
      (Ω := Ω) (fine := fine) (hist := hist) (pre := pre) (item := item)
      (suffix := suffix) (coarseCell := coarseCell) refn hbad
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hfieldedBad,
      not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hfieldedBad⟩

end Mettapedia.Computability.PNP
