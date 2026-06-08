import Mettapedia.Computability.PNP.PNPv13ACCEIEnvelope

/-!
# Regression checks for PNP v13 ACCEI envelope skeleton

These checks pin the finite Markov-pruning and generic tower-product theorem
surface used to audit the v13 ACCEI/PNLD route.
-/

namespace Mettapedia.Computability.PNP.PNPv13ACCEIEnvelopeRegression

open Mettapedia.Computability.PNP
open scoped BigOperators

universe u

theorem accei_good_bad_partition_regression
    (ι : Type u) [Fintype ι] (η : ι → ℕ) (threshold : ℕ) :
    acceiGoodCount ι η threshold + acceiBadCount ι η threshold =
      Fintype.card ι := by
  exact acceiGoodCount_add_acceiBadCount ι η threshold

theorem accei_markov_bad_count_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    acceiBadCount ι η threshold * (threshold + 1) ≤ budget := by
  exact acceiBadCount_mul_succ_threshold_le_of_sum_le
    η threshold budget hbudget

theorem accei_bad_count_complement_regression
    (ι : Type u) [Fintype ι] (η : ι → ℕ) (threshold : ℕ) :
    acceiBadCount ι η threshold =
      Fintype.card ι - acceiGoodCount ι η threshold := by
  exact acceiBadCount_eq_card_sub_acceiGoodCount ι η threshold

theorem accei_markov_complement_bound_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    (Fintype.card ι - acceiGoodCount ι η threshold) *
        (threshold + 1) ≤ budget := by
  exact card_sub_acceiGoodCount_mul_succ_threshold_le_of_sum_le
    η threshold budget hbudget

theorem accei_markov_bad_count_div_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    acceiBadCount ι η threshold ≤ budget / (threshold + 1) := by
  exact acceiBadCount_le_budget_div_succ_threshold_of_sum_le
    η threshold budget hbudget

theorem accei_good_count_large_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    Fintype.card ι - budget / (threshold + 1) ≤
      acceiGoodCount ι η threshold := by
  exact card_sub_budget_div_succ_threshold_le_acceiGoodCount_of_sum_le
    η threshold budget hbudget

theorem accei_exists_good_of_small_loss_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget)
    (hloss : budget / (threshold + 1) < Fintype.card ι) :
    ∃ i : ι, η i ≤ threshold := by
  exact exists_accei_good_of_budget_div_succ_threshold_lt_card
    η threshold budget hbudget hloss

theorem accei_one_good_one_bad_sum_regression (threshold : ℕ) :
    (∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b) =
      threshold + 1 := by
  exact oneGoodOneBadACCEIEnvelope_sum threshold

theorem accei_one_good_one_bad_count_regression (threshold : ℕ) :
    acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold = 1 ∧
      acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold = 1 := by
  exact
    ⟨oneGoodOneBadACCEIEnvelope_goodCount threshold,
      oneGoodOneBadACCEIEnvelope_badCount threshold⟩

theorem accei_one_good_one_bad_markov_sharp_regression (threshold : ℕ) :
    acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
        (threshold + 1) =
      ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b := by
  exact oneGoodOneBadACCEIEnvelope_markov_badCount_sharp threshold

theorem accei_one_good_one_bad_good_lower_bound_sharp_regression
    (threshold : ℕ) :
    Fintype.card Bool - (threshold + 1) / (threshold + 1) =
      acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold := by
  exact oneGoodOneBadACCEIEnvelope_good_lower_bound_sharp threshold

theorem accei_one_good_one_bad_not_all_good_regression (threshold : ℕ) :
    ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold := by
  exact oneGoodOneBadACCEIEnvelope_not_all_good threshold

theorem accei_all_good_of_small_sum_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold : ℕ)
    (hsum : (∑ i, η i) < threshold + 1) :
    ∀ i : ι, η i ≤ threshold := by
  exact all_accei_good_of_sum_lt_succ_threshold η threshold hsum

theorem prefix_rate_step_from_sequential_rate_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    {numerator denominator : ℕ}
    (h : SequentialRateAdmissibleFrom hist (E :: rest) numerator denominator) :
    PrefixRateStep hist E numerator denominator := by
  exact prefixRateStep_of_sequentialRateAdmissibleFrom_cons h

theorem failed_prefix_rate_step_blocks_sequential_rate_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    {numerator denominator : ℕ}
    (hfail : ¬ PrefixRateStep hist E numerator denominator) :
    ¬ SequentialRateAdmissibleFrom hist (E :: rest) numerator denominator := by
  exact not_sequentialRateAdmissibleFrom_cons_of_not_prefixRateStep hfail

theorem sequential_rate_product_bound_regression
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω)) (numerator denominator : ℕ)
    (h : SequentialRateAdmissibleFrom hist rest numerator denominator) :
    denominator ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
      numerator ^ rest.length * finiteHistoryCount Ω hist := by
  exact finiteHistory_product_bound_of_sequentialRateFrom
    hist rest numerator denominator h

theorem sequential_rate_product_bound_empty_history_regression
    {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω)) (numerator denominator : ℕ)
    (h : SequentialRateAdmissible events numerator denominator) :
    denominator ^ events.length * finiteHistoryCount Ω events ≤
      numerator ^ events.length *
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact finiteHistory_product_bound_of_sequentialRate
    events numerator denominator h

theorem sequential_rate_contrapositive_regression
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
        numerator ^ rest.length * finiteHistoryCount Ω hist) :
    ¬ SequentialRateAdmissibleFrom hist rest numerator denominator := by
  exact not_sequentialRateAdmissibleFrom_of_product_bound_violation hbad

theorem failed_prefix_rate_from_not_sequential_rate_regression
    {Ω : Type u} [Fintype Ω]
    {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hfail : ¬ SequentialRateAdmissibleFrom hist events numerator denominator) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep (hist ++ pre) E numerator denominator := by
  exact
    exists_failed_prefixRateStep_at_append_cons_of_not_sequentialRateAdmissibleFrom
      hfail

theorem failed_prefix_rate_from_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ events.length *
            finiteHistoryCount Ω (hist ++ events) ≤
          numerator ^ events.length * finiteHistoryCount Ω hist) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep (hist ++ pre) E numerator denominator := by
  exact
    exists_failed_prefixRateStep_at_append_cons_of_product_bound_violation
      hbad

theorem failed_prefix_rate_from_empty_product_bound_violation_regression
    {Ω : Type u} [Fintype Ω]
    {events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ events.length * finiteHistoryCount Ω events ≤
        numerator ^ events.length *
          finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep pre E numerator denominator := by
  exact
    exists_failed_prefixRateStep_at_append_cons_of_empty_product_bound_violation
      hbad

theorem half_step_specializes_to_rate_regression
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissibleFrom hist rest) :
    SequentialRateAdmissibleFrom hist rest 1 2 := by
  exact sequentialRateAdmissibleFrom_one_two_of_sequentialHalfAdmissibleFrom
    hist rest h

end Mettapedia.Computability.PNP.PNPv13ACCEIEnvelopeRegression
