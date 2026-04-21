import Mettapedia.Computability.PNP.FiniteSwitchingAdmissibility

/-!
# Regression checks for finite switching admissibility

These checks pin the generic finite tower-product theorem surface without
forcing regression builds to evaluate concrete subtype cardinalities.
-/

namespace Mettapedia.Computability.PNP.FiniteSwitchingAdmissibilityRegression

open Mettapedia.Computability.PNP

universe u

theorem finite_event_count_mono_regression
    {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) :
    finiteEventCount Ω E ≤ finiteEventCount Ω F := by
  exact finiteEventCount_le_of_imp h

theorem finite_history_count_append_le_regression
    {Ω : Type u} [Fintype Ω]
    (hist tail : List (FiniteEvent Ω)) :
    finiteHistoryCount Ω (hist ++ tail) ≤ finiteHistoryCount Ω hist := by
  exact finiteHistoryCount_append_le hist tail

theorem prefix_half_step_of_zero_history_regression
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} (E : FiniteEvent Ω)
    (hzero : finiteHistoryCount Ω hist = 0) :
    PrefixHalfStep hist E := by
  exact prefixHalfStep_of_historyCount_eq_zero E hzero

theorem finite_history_product_bound_from_prefix_regression
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissibleFrom hist rest) :
    2 ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
      finiteHistoryCount Ω hist := by
  exact finiteHistory_product_bound_of_sequentialHalfFrom hist rest h

theorem finite_history_product_bound_regression
    {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissible events) :
    2 ^ events.length * finiteHistoryCount Ω events ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact finiteHistory_product_bound_of_sequentialHalf events h

theorem product_bound_violation_blocks_sequential_half_from_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)}
    (hbad :
      ¬ 2 ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
        finiteHistoryCount Ω hist) :
    ¬ SequentialHalfAdmissibleFrom hist rest := by
  exact not_sequentialHalfAdmissibleFrom_of_product_bound_violation hbad

theorem product_bound_violation_blocks_sequential_half_regression
    {Ω : Type u} [Fintype Ω]
    {events : List (FiniteEvent Ω)}
    (hbad :
      ¬ 2 ^ events.length * finiteHistoryCount Ω events ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ SequentialHalfAdmissible events := by
  exact not_sequentialHalfAdmissible_of_product_bound_violation hbad

theorem prefix_half_step_from_cons_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    (h : SequentialHalfAdmissibleFrom hist (E :: rest)) :
    PrefixHalfStep hist E := by
  exact prefixHalfStep_of_sequentialHalfAdmissibleFrom_cons h

theorem failed_prefix_half_step_blocks_tail_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    (hfail : ¬ PrefixHalfStep hist E) :
    ¬ SequentialHalfAdmissibleFrom hist (E :: rest) := by
  exact not_sequentialHalfAdmissibleFrom_cons_of_not_prefixHalfStep hfail

theorem failed_second_prefix_half_step_blocks_pair_regression
    {Ω : Type u} [Fintype Ω] {E F : FiniteEvent Ω}
    (hfail : ¬ PrefixHalfStep [E] F) :
    ¬ SequentialHalfAdmissible [E, F] := by
  exact not_sequentialHalfAdmissible_pair_of_not_second_prefixHalfStep hfail

end Mettapedia.Computability.PNP.FiniteSwitchingAdmissibilityRegression
