import Mettapedia.Computability.PNP.PNPv13FieldRefinement

/-!
# PNP v13 field-refinement obstruction for failed coarse prefixes

The earlier refinement files isolated two specific ways a coarse field can fail:
an explicit bad cell, and support-relative success determination on positive
mass.  This file abstracts the route-facing consequence.  Once a coarse field
already fails the fixed-field prefix obligation at a given accumulated history,
no genuine refinement of that field can rescue the prefix or the whole fixed
field route at that position.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- Refinement is monotone for failure of the fixed-field prefix obligation:
if a coarse field already fails on one history/step pair, then every genuine
refinement fails there as well. -/
theorem not_v13FieldPrefixInstantiation_of_refinement_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hfail : ¬ V13FieldPrefixInstantiation coarse hist step) :
    ¬ V13FieldPrefixInstantiation fine hist step := by
  rcases exists_bad_cell_of_not_v13FieldPrefixInstantiation
      (field := coarse) (hist := hist) (step := step) hfail with
    ⟨coarseCell, hbad⟩
  exact
    not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell
      (Ω := Ω) (fine := fine) (coarse := coarse)
      (hist := hist) (step := step) (coarseCell := coarseCell) refn hbad

/-- A failed coarse fixed-field prefix certificate at an explicit later
position still blocks the refined fielded switching route. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_refinement_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hfail :
      ¬ V13FieldPrefixInstantiation coarse
          (hist ++ v13FieldedSuccessEvents pre) step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist)
      (pre := pre)
      (item := ({ field := fine, step := step } : V13FieldedStep Ω))
      (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_refinement_not_fieldPrefixInstantiation
        (Ω := Ω) (fine := fine) (coarse := coarse)
        (hist := hist ++ v13FieldedSuccessEvents pre) (step := step) refn hfail)

/-- The same coarse failed-prefix premise also blocks the equivalent recursive
same-cell matching route after refinement. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_refinement_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hfail :
      ¬ V13FieldPrefixInstantiation coarse
          (hist ++ v13FieldedSuccessEvents pre) step) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist
      (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix) := by
  intro hmatch
  have hlocal :
      V13FieldFailureMatching fine
        (hist ++ v13FieldedSuccessEvents pre) step := by
    simpa using
      v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
        (hist := hist)
        (pre := pre)
        (item := ({ field := fine, step := step } : V13FieldedStep Ω))
        (suffix := suffix)
        hmatch
  have hprefix :
      V13FieldPrefixInstantiation fine
        (hist ++ v13FieldedSuccessEvents pre) step :=
    v13FieldPrefixInstantiation_of_failureMatching hlocal
  exact
    (not_v13FieldPrefixInstantiation_of_refinement_not_fieldPrefixInstantiation
      (Ω := Ω) (fine := fine) (coarse := coarse)
      (hist := hist ++ v13FieldedSuccessEvents pre) (step := step) refn hfail)
      hprefix

/-- Route-level synthesis form: once the coarse prefix already fails, field
refinement alone cannot repair either fixed-field formulation at that
position. -/
theorem v13FieldRefinementFailedPrefix_blocks_fixedFieldRoute_at
    {Ω : Type u} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (refn : V13HistoryFieldRefinement fine coarse)
    (hfail :
      ¬ V13FieldPrefixInstantiation coarse
          (hist ++ v13FieldedSuccessEvents pre) step) :
    (¬ V13FieldSwitchingInstantiatedFrom hist
        (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix)) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist
        (pre ++ ({ field := fine, step := step } : V13FieldedStep Ω) :: suffix) := by
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_append_cons_of_refinement_not_fieldPrefixInstantiation
        (Ω := Ω) (fine := fine) (coarse := coarse)
        (hist := hist) (pre := pre) (step := step) (suffix := suffix) refn hfail,
      not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_refinement_not_fieldPrefixInstantiation
        (Ω := Ω) (fine := fine) (coarse := coarse)
        (hist := hist) (pre := pre) (step := step) (suffix := suffix) refn hfail⟩

end Mettapedia.Computability.PNP
