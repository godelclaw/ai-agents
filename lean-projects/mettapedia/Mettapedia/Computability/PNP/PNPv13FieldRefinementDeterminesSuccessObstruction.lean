import Mettapedia.Computability.PNP.PNPv13FieldRefinement

/-!
# PNP v13 field-refinement obstruction for success-determining fields

If a coarse fixed history field already determines the next success event on
the current history support, then refining that field cannot help: every fine
cell sits inside a single coarse cell, so the finer field is still
success-determining on the same support.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- Success determination is monotone under field refinement: if a coarse field
already reveals the next success event globally, then any genuine refinement
does too. -/
theorem v13HistoryFieldDeterminesSuccess_of_refinement
    {Ω : Type u}
    {fine coarse : V13HistoryField Ω} {step : V13SwitchedStep Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hdet : V13HistoryFieldDeterminesSuccess coarse step) :
    V13HistoryFieldDeterminesSuccess fine step := by
  intro ω ω' hcell hsucc
  exact hdet
    (calc
      coarse.cellOf ω = refn.project (fine.cellOf ω) :=
        (refn.cellOf_project ω).symm
      _ = refn.project (fine.cellOf ω') := by rw [hcell]
      _ = coarse.cellOf ω' := refn.cellOf_project ω')
    hsucc

/-- Prefix-relative success determination is also monotone under refinement:
conditioning on a history support does not change the fact that every fine cell
lies inside one coarse cell. -/
theorem v13HistoryFieldDeterminesSuccessOn_of_refinement
    {Ω : Type u}
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hdet : V13HistoryFieldDeterminesSuccessOn coarse hist step) :
    V13HistoryFieldDeterminesSuccessOn fine hist step := by
  intro ω ω' hω hω' hcell hsucc
  exact hdet hω hω'
    (calc
      coarse.cellOf ω = refn.project (fine.cellOf ω) :=
        (refn.cellOf_project ω).symm
      _ = refn.project (fine.cellOf ω') := by rw [hcell]
      _ = coarse.cellOf ω' := refn.cellOf_project ω')
    hsucc

/-- Consequently, refining a support-relative success-determining field cannot
produce a fixed-field prefix certificate on a positive-mass next-success
history. -/
theorem not_v13FieldPrefixInstantiation_of_refinement_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hdet : V13HistoryFieldDeterminesSuccessOn coarse hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation fine hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_refinement refn hdet) hpos

/-- Therefore a refined fielded suffix is blocked as soon as the coarse field
already determines the next success event on the current support with positive
next-success mass. -/
theorem v13FieldRefinementDeterminesSuccessOnPositive_blocks_fixedFieldRoute_at
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hdet :
      V13HistoryFieldDeterminesSuccessOn coarse
        (hist ++ v13FieldedSuccessEvents pre) step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [step.successEvent])) :
    (¬ V13FieldSwitchingInstantiatedFrom hist
        (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix)) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist
        (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix) := by
  refine ⟨?_, ?_⟩
  · exact
      not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
        (hist := hist) (pre := pre)
        (item := ({ field := fine, step := step } : V13FieldedStep Ω))
        (suffix := suffix)
        (hdet := v13HistoryFieldDeterminesSuccessOn_of_refinement refn hdet)
        hpos
  · exact
      not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
        (hist := hist) (pre := pre)
        (item := ({ field := fine, step := step } : V13FieldedStep Ω))
        (suffix := suffix)
        (hdet := v13HistoryFieldDeterminesSuccessOn_of_refinement refn hdet)
        hpos

end Mettapedia.Computability.PNP
