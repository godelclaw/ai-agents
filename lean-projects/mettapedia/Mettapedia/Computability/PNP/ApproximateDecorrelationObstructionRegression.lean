import Mettapedia.Computability.PNP.ApproximateDecorrelationObstruction

/-!
# Regression checks for approximate decorrelation obstructions

These wrappers pin the quantitative finite-count obstruction: coupled and
anti-coupled conditioning surfaces have explicit nonzero cross-product defects
whenever both conditioned source-bit fibers are populated.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coupled_forward_gap_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    countIndependentWithinForwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact countIndependentWithinForwardGap_coupled C E F hcouple

theorem anticoupled_backward_gap_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    countIndependentWithinBackwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact countIndependentWithinBackwardGap_anticoupled C E F hanti

theorem coupled_nonconstant_forward_gap_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinForwardGap (Ω := Ω) C E F := by
  exact
    countIndependentWithinForwardGap_pos_of_coupled_nonconstant_on_condition
      C E F hcouple hpos hneg

theorem anticoupled_nonconstant_backward_gap_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinBackwardGap (Ω := Ω) C E F := by
  exact
    countIndependentWithinBackwardGap_pos_of_anticoupled_nonconstant_on_condition
      C E F hanti hpos hneg

theorem nonconstant_source_fiber_product_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact conditionedSourceFiberProduct_pos_of_nonconstant_on_condition C E hpos hneg

theorem lower_bounds_multiply_into_source_fiber_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    loTrue * loFalse ≤ conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact lowerBounds_mul_le_conditionedSourceFiberProduct
    C E loTrue loFalse htrue hfalse

theorem finite_event_count_fst_lift_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) [DecidablePred P] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1) =
      finiteEventCount Ω P * Fintype.card Coin := by
  exact finiteEventCount_fst_lift P

theorem finite_event_count_fst_lift_pos_of_pos_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    (P : Ω → Prop) [DecidablePred P]
    (hpos : 0 < finiteEventCount Ω P) :
    0 < finiteEventCount (Ω × Coin) (fun xr => P xr.1) := by
  exact finiteEventCount_fst_lift_pos_of_pos P hpos

theorem finite_event_count_prod_regression
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1 ∧ Q xr.2) =
      finiteEventCount Ω P * finiteEventCount Coin Q := by
  exact finiteEventCount_prod P Q

theorem finite_event_count_eq_self_regression
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    finiteEventCount α (fun x => x = a) = 1 := by
  exact finiteEventCount_eq_self a

theorem finite_event_count_zero_of_forall_not_regression
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P]
    (hfalse : ∀ ω, ¬ P ω) :
    finiteEventCount Ω P = 0 := by
  exact finiteEventCount_zero_of_forall_not P hfalse

theorem finite_event_count_comp_eq_sum_fibers_of_maps_to_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Coin → α) (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hr : ∀ c : Coin, r c ∈ s) :
    finiteEventCount Coin (fun c => P (r c)) =
      ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y) := by
  exact finiteEventCount_comp_eq_sum_fibers_of_mapsTo r s P hr

theorem finite_event_count_bool_true_add_false_regression
    {Ω : Type*} [Fintype Ω] (B : Ω → Bool) :
    finiteEventCount Ω (fun ω => B ω = true) +
      finiteEventCount Ω (fun ω => B ω = false) = Fintype.card Ω := by
  exact finiteEventCount_bool_true_add_false B

theorem finite_coin_recoding_true_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_trueFiber C E r y

theorem finite_coin_recoding_false_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_falseFiber C E r y

theorem finite_coin_recoding_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_forward_gap_imbalance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  exact countIndependentWithinForwardGap_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_backward_gap_imbalance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  exact countIndependentWithinBackwardGap_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_balanced_fibers_exactly_decorrelate_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
    C E r hbal

theorem coin_true_fiber_count_self_positive_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    0 < coinTrueFiberCount r (r true c₀) := by
  exact coinTrueFiberCount_self_pos r c₀

theorem balanced_finite_coin_recoding_blocks_output_predicate_at_coin_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) (c₀ : Coin)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r P c₀ htrue hfalse

theorem balanced_finite_coin_recoding_blocks_nonempty_output_predicate_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates
      r P htrue hfalse

theorem balanced_finite_coin_recoding_output_predicate_counts_match_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => P (r true c)) =
      finiteEventCount Coin (fun c => P (r false c)) := by
  exact finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal

theorem balanced_finite_coin_recoding_blocks_true_count_advantage_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_trueCount_gt_falseCount
      r P hgt

theorem balanced_finite_coin_recoding_blocks_false_count_advantage_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_falseCount_gt_trueCount
      r P hgt

theorem balanced_finite_coin_recoding_decoder_correct_count_half_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => decode (r true c) = true) +
      finiteEventCount Coin (fun c => decode (r false c) = false) =
        Fintype.card Coin := by
  exact finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
    r decode hbal

theorem balanced_finite_coin_recoding_blocks_decoder_better_than_half_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin <
      finiteEventCount Coin (fun c => decode (r true c) = true) +
        finiteEventCount Coin (fun c => decode (r false c) = false)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_correctCount_gt_card
      r decode hgt

theorem balanced_finite_coin_recoding_blocks_output_decoder_at_coin_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool) (c₀ : Coin)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
      r decode c₀ htrue hfalse

theorem balanced_finite_coin_recoding_blocks_nonempty_output_decoder_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers
      r decode htrue hfalse

theorem finite_coin_recoding_true_minus_false_imbalance_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  exact
    trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox

theorem finite_coin_recoding_false_minus_true_imbalance_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  exact
    falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox

theorem finite_coin_recoding_true_minus_false_imbalance_blocks_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_trueMinusFalse_gt
      C E r y τ htol

theorem finite_coin_recoding_false_minus_true_imbalance_blocks_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_falseMinusTrue_gt
      C E r y τ htol

theorem finite_coin_recoding_true_minus_false_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  exact
    sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox

theorem finite_coin_recoding_false_minus_true_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  exact
    sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox

theorem finite_coin_recoding_true_minus_false_source_lower_bounds_block_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_trueMinusFalse_gt
      C E r y τ loTrue loFalse htrue hfalse htol

theorem finite_coin_recoding_false_minus_true_source_lower_bounds_block_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_falseMinusTrue_gt
      C E r y τ loTrue loFalse htrue hfalse htol

theorem finite_coin_recoding_source_lower_bounds_lt_coin_product_forces_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r htrue hfalse happrox hlt

theorem finite_coin_recoding_source_lower_bounds_lt_coin_product_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r htrue hfalse hlt

theorem finite_coin_recoding_lt_source_coin_product_forces_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_sourceCoinProduct
      C E r happrox hlt

theorem finite_coin_recoding_lt_source_coin_product_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_lt_sourceCoinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r hlt

theorem finite_coin_recoding_coin_retained_balanced_iff_pointwise_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) ↔
      ∀ c : Coin, r true c = r false c := by
  exact finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq r

theorem finite_coin_recoding_coin_retained_source_lower_bounds_lt_coin_product_iff_pointwise_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
      C E r htrue hfalse hlt

theorem finite_coin_recoding_coin_retained_lt_source_coin_product_iff_pointwise_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_lt_sourceCoinProduct_iff_pointwise_eq
      C E r hlt

theorem finite_coin_recoding_side_retained_balanced_iff_side_fiber_count_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) ↔
      ∀ (y : α) (s : Side),
        finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq r side

theorem finite_coin_recoding_side_retained_source_lower_bounds_lt_coin_product_iff_side_fiber_count_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
      C E r side htrue hfalse hlt

theorem finite_coin_recoding_side_retained_lt_source_coin_product_iff_side_fiber_count_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_lt_sourceCoinProduct_iff_sideFiber_count_eq
      C E r side hlt

theorem finite_coin_recoding_true_minus_false_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinFalseFiberCount r y < coinTrueFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
      C E r y hpos hneg himb

theorem finite_coin_recoding_false_minus_true_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinTrueFiberCount r y < coinFalseFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
      C E r y hpos hneg himb

theorem finite_coin_recoding_source_nonconstant_zero_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
      C E r hpos hneg

theorem coin_true_fiber_count_with_coin_true_fiber_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 1 := by
  exact coinTrueFiberCount_withCoin_trueFiber r c₀

theorem coin_false_fiber_count_with_coin_true_fiber_empty_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    coinFalseFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 0 := by
  exact coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep

theorem coin_retained_true_fiber_forward_gap_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin := by
  exact countIndependentWithinForwardGap_coinRetained_trueFiber C E r c₀ hsep

theorem coin_retained_true_fiber_output_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox

theorem coin_retained_true_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ loTrue loFalse hsep htrue hfalse happrox

theorem coin_retained_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceProduct_gt
      C E r c₀ τ hsep htol

theorem coin_retained_true_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse * Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceLowerBounds_mul_gt
      C E r c₀ τ loTrue loFalse hsep htrue hfalse htol

theorem coin_true_fiber_count_with_side_true_fiber_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  exact coinTrueFiberCount_withSide_trueFiber r side c₀

theorem coin_false_fiber_count_with_side_true_fiber_empty_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) = 0 := by
  exact coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    r side c₀ hsep

theorem side_retained_true_fiber_forward_gap_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  exact countIndependentWithinForwardGap_sideRetained_trueFiber
    C E r side c₀ hsep

theorem side_retained_true_fiber_output_forces_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r true c = r true c₀ ∧ side c = side c₀) ≤ τ := by
  exact
    sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox

theorem side_retained_true_fiber_source_side_lower_bounds_force_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact
    sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox

theorem side_retained_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r true c = r true c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_product_gt
      C E r side c₀ τ hsep htol

theorem side_retained_true_fiber_source_side_lower_bounds_block_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_sourceSideLowerBounds_mul_gt
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside htol

theorem coin_false_fiber_count_with_side_false_fiber_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  exact coinFalseFiberCount_withSide_falseFiber r side c₀

theorem coin_true_fiber_count_with_side_false_fiber_empty_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) = 0 := by
  exact coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    r side c₀ hsep

theorem side_retained_false_fiber_backward_gap_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  exact countIndependentWithinBackwardGap_sideRetained_falseFiber
    C E r side c₀ hsep

theorem side_retained_false_fiber_output_forces_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r false c = r false c₀ ∧ side c = side c₀) ≤ τ := by
  exact
    sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox

theorem side_retained_false_fiber_source_side_lower_bounds_force_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact
    sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox

theorem side_retained_false_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r false c = r false c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_product_gt
      C E r side c₀ τ hsep htol

theorem side_retained_false_fiber_source_side_lower_bounds_block_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_sourceSideLowerBounds_mul_gt
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside htol

theorem finite_coin_recoding_postprocessed_side_balanced_iff_observed_fiber_count_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
    r side post

theorem finite_coin_recoding_postprocessed_side_source_lower_bounds_lt_coin_product_iff_observed_fiber_count_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
      C E r side post htrue hfalse hlt

theorem finite_coin_recoding_postprocessed_side_lt_source_coin_product_iff_observed_fiber_count_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_observedFiber_count_eq
      C E r side post hlt

theorem postprocessed_side_observed_fiber_imbalance_products_lower_bound_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) := by
  exact
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox

theorem postprocessed_side_true_minus_false_observed_fiber_source_lower_bounds_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_trueMinusFalse_sourceLowerBounds_gt
      C E r side post z τ loTrue loFalse htrue hfalse htol

theorem postprocessed_side_false_minus_true_observed_fiber_source_lower_bounds_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_falseMinusTrue_sourceLowerBounds_gt
      C E r side post z τ loTrue loFalse htrue hfalse htol

theorem postprocessed_side_output_predicate_count_eq_of_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox

theorem postprocessed_side_output_predicate_true_advantage_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) <
        finiteEventCount Coin (fun c => P (post (r true c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt hgt

theorem postprocessed_side_output_predicate_false_advantage_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) <
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_falseCount_gt_trueCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt hgt

theorem postprocessed_side_output_predicate_separates_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (htruePred : ∀ c : Coin, P (post (r true c, side c)))
    (hfalsePred : ∀ c : Coin, ¬ P (post (r false c, side c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt htruePred hfalsePred

theorem postprocessed_side_output_decoder_correct_count_eq_card_of_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  exact
    postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt happrox

theorem postprocessed_side_output_decoder_better_than_half_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      Fintype.card Coin <
        finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
          finiteEventCount Coin
            (fun c => decode (post (r false c, side c)) = false)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_gt_card_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt hgt

theorem postprocessed_side_output_decoder_recovers_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

theorem postprocessed_side_source_ranges_separated_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hsep

theorem postprocessed_side_true_false_collision_obligation_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  exact
    exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

theorem postprocessed_side_pointwise_collision_obligation_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) := by
  exact
    postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

theorem postprocessed_side_pointwise_collision_skew_pointwise_regression :
    (∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) := by
  exact postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions

theorem postprocessed_side_pointwise_collision_skew_no_matching_regression :
    ¬ ∃ e : Fin 3 ≃ Fin 3,
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (e c) := by
  exact postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving

theorem postprocessed_side_pointwise_collisions_not_enough_for_matching_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving

theorem postprocessed_side_injective_coin_map_promotes_to_matching_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hinj : Function.Injective f) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
      r side post f hpres hinj

theorem postprocessed_side_no_matching_forces_one_sided_map_noninjective_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      r side post f hpres hno

theorem postprocessed_side_injective_coin_map_iff_matching_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
      r side post

theorem postprocessed_side_injective_coin_map_iff_observed_fiber_count_eq_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
      r side post

theorem postprocessed_side_observed_fiber_mismatch_forces_one_sided_map_noninjective_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_observedFiber_count_ne
      r side post f hpres z hne

theorem postprocessed_side_pointwise_collision_skew_true_to_false_map_regression :
    ∀ c : Fin 3,
      postprocessedSidePointwiseCollisionSkewRecoding true c =
        postprocessedSidePointwiseCollisionSkewRecoding false
          (postprocessedSidePointwiseCollisionSkewTrueToFalseMap c) := by
  exact postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving

theorem postprocessed_side_pointwise_collision_skew_true_to_false_map_not_injective_regression :
    ¬ Function.Injective postprocessedSidePointwiseCollisionSkewTrueToFalseMap := by
  exact postprocessedSidePointwiseCollisionSkew_trueToFalseMap_not_injective

theorem postprocessed_side_pointwise_collision_skew_any_preserving_map_not_injective_regression
    (f : Fin 3 → Fin 3)
    (hpres :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (f c)) :
    ¬ Function.Injective f := by
  exact
    postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective
      f hpres

theorem postprocessed_side_one_sided_coin_map_not_enough_for_matching_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving

theorem postprocessed_side_coin_matching_obligation_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

theorem postprocessed_side_no_coin_matching_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hno

theorem postprocessed_side_coin_matching_preserves_observed_fiber_counts_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
    r side post e hpres

theorem postprocessed_side_observed_fiber_count_mismatch_blocks_coin_matching_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
      r side post z hne

theorem postprocessed_side_observed_fiber_count_mismatch_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
      C E r side post z htrue hfalse hlt hne

theorem postprocessed_side_pointwise_collision_skew_true_count_true_regression :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) = 2 := by
  exact postprocessedSidePointwiseCollisionSkew_true_count_true

theorem postprocessed_side_pointwise_collision_skew_false_count_true_regression :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) = 1 := by
  exact postprocessedSidePointwiseCollisionSkew_false_count_true

theorem postprocessed_side_pointwise_collision_skew_not_count_independent_lt_three_regression
    {τ : Nat} (htol : τ < 3) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
      htol

theorem postprocessed_side_pointwise_collision_skew_true_forward_gap_eq_three_regression :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 3 := by
  exact postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three

theorem postprocessed_side_pointwise_collision_skew_false_backward_gap_eq_three_regression :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 3 := by
  exact postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three

theorem postprocessed_side_pointwise_collision_skew_count_independent_three_le_regression
    {τ : Nat} (hτ : 3 ≤ τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le
      hτ

theorem postprocessed_side_pointwise_collision_skew_count_independent_iff_three_le_regression
    {τ : Nat} :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ ↔
      3 ≤ τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_iff_three_le

theorem postprocessed_side_pointwise_collision_skew_counterexample_of_two_regression :
    ((∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse)) ∧
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true c =
            postprocessedSidePointwiseCollisionSkewRecoding false (f c)) ∧
      ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
        (fun _xr => True)
        (fun xr => xr.1 = true)
        (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) 2 := by
  exact
    postprocessedSidePointwiseCollisionSkew_collision_and_oneSidedMap_counterexample_of_lt_three
      (by decide)

theorem postprocessed_side_coin_matching_preserves_output_predicate_counts_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post P e hpres

theorem postprocessed_side_output_predicate_count_mismatch_blocks_coin_matching_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    not_exists_postprocessedSide_coinEquiv_preserving_of_outputPredicate_count_ne
      r side post P hne

theorem postprocessed_side_output_predicate_count_mismatch_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_count_ne_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt hne

theorem postprocessed_side_coin_matching_forces_decoder_half_accuracy_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  exact
    postprocessedSide_outputDecoder_correctCount_eq_card_of_coinEquiv_preserving
      r side post decode e hpres

theorem postprocessed_side_decoder_not_half_blocks_coin_matching_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    not_exists_postprocessedSide_coinEquiv_preserving_of_outputDecoder_correctCount_ne_card
      r side post decode hne

theorem postprocessed_side_decoder_not_half_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_ne_card_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt hne

theorem postprocessed_side_output_predicate_count_eq_iff_observed_fiber_count_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∀ P : β → Prop, [DecidablePred P] →
      finiteEventCount Coin (fun c => P (post (r true c, side c))) =
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
    r side post

theorem postprocessed_side_coin_matching_iff_output_predicate_count_eq_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact exists_postprocessedSide_coinEquiv_preserving_iff_outputPredicate_count_eq
    r side post

theorem postprocessed_side_coin_matching_iff_observed_fiber_count_eq_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact exists_postprocessedSide_coinEquiv_preserving_iff_observedFiber_count_eq
    r side post

theorem postprocessed_side_source_lower_bounds_lt_coin_product_iff_output_predicate_count_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_outputPredicate_count_eq
      C E r side post htrue hfalse hlt

theorem postprocessed_side_source_lower_bounds_lt_coin_product_iff_coin_equiv_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
      C E r side post htrue hfalse hlt

theorem postprocessed_side_lt_source_coin_product_iff_coin_equiv_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_coinEquiv_preserving
      C E r side post hlt

theorem coin_false_fiber_count_postprocessed_side_true_fiber_empty_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    coinFalseFiberCount (fun b c => post (r b c, side c))
        (post (r true c₀, side c₀)) = 0 := by
  exact coinFalseFiberCount_postprocessedSide_trueFiber_eq_zero_of_forall_ne
    r side post c₀ hsep

theorem postprocessed_side_true_fiber_forward_gap_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r true c, side c) = post (r true c₀, side c₀)) := by
  exact countIndependentWithinForwardGap_postprocessedSide_trueFiber
    C E r side post c₀ hsep

theorem postprocessed_side_true_fiber_output_forces_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r true c, side c) = post (r true c₀, side c₀)) ≤ τ := by
  exact
    postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ hsep happrox

theorem postprocessed_side_true_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact
    sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox

theorem postprocessed_side_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r true c, side c) = post (r true c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_product_gt
      C E r side post c₀ τ hsep htol

theorem postprocessed_side_true_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_sourceLowerBounds_mul_gt
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs htol

theorem coin_true_fiber_count_postprocessed_side_false_fiber_empty_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    coinTrueFiberCount (fun b c => post (r b c, side c))
        (post (r false c₀, side c₀)) = 0 := by
  exact coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    r side post c₀ hsep

theorem postprocessed_side_false_fiber_backward_gap_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r false c, side c) = post (r false c₀, side c₀)) := by
  exact countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    C E r side post c₀ hsep

theorem postprocessed_side_false_fiber_output_forces_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r false c, side c) = post (r false c₀, side c₀)) ≤ τ := by
  exact
    postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox

theorem postprocessed_side_false_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact
    sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox

theorem postprocessed_side_false_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r false c, side c) = post (r false c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_product_gt
      C E r side post c₀ τ hsep htol

theorem postprocessed_side_false_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_sourceLowerBounds_mul_gt
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs htol

theorem coupled_product_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_coupled_product_gt
      C E F τ hcouple htol

theorem anticoupled_product_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_anticoupled_product_gt
      C E F τ hanti htol

theorem coupled_approx_certificate_forces_product_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      C E F τ hcouple happrox

theorem coupled_lower_bounds_force_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
      C E F τ loTrue loFalse hcouple htrue hfalse happrox

theorem coupled_lower_bounds_block_smaller_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_coupled_lowerBounds_mul_gt
      C E F τ loTrue loFalse hcouple htrue hfalse htol

theorem anticoupled_approx_certificate_forces_product_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ hanti happrox

theorem anticoupled_lower_bounds_force_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ loTrue loFalse hanti htrue hfalse happrox

theorem anticoupled_lower_bounds_block_smaller_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_anticoupled_lowerBounds_mul_gt
      C E F τ loTrue loFalse hanti htrue hfalse htol

theorem bool_to_any_recoding_true_side_fiber_forward_gap_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true = y) (hf : r false ≠ y) :
    countIndependentWithinForwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact
    countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
      C E r y ht hf

theorem bool_to_any_recoding_false_side_fiber_backward_gap_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true ≠ y) (hf : r false = y) :
    countIndependentWithinBackwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact
    countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
      C E r y ht hf

theorem bool_to_any_recoding_true_side_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true = y) (hf : r false ≠ y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
      C E r y τ ht hf htol

theorem bool_to_any_recoding_false_side_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true ≠ y) (hf : r false = y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
      C E r y τ ht hf htol

theorem bool_to_any_recoding_distinguishing_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y τ hdistinguish htol

theorem bool_to_any_recoding_distinguishing_fiber_approx_forces_product_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ hdistinguish happrox

theorem bool_to_any_recoding_distinguishing_fiber_lower_bounds_force_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ loTrue loFalse hdistinguish htrue hfalse happrox

theorem bool_to_any_recoding_distinguishing_fiber_lower_bounds_block_smaller_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_lowerBounds_mul_gt
      C E r y τ loTrue loFalse hdistinguish htrue hfalse htol

theorem bool_to_any_recoding_output_approx_forces_product_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox

theorem bool_to_any_recoding_output_lower_bounds_force_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ loTrue loFalse hnonconst htrue hfalse happrox

theorem bool_to_any_recoding_output_product_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
      C E r τ hnonconst htol

theorem bool_to_any_recoding_output_lower_bounds_block_smaller_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_lowerBounds_mul_gt
      C E r τ loTrue loFalse hnonconst htrue hfalse htol

theorem coinwise_true_fiber_output_approx_forces_product_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_false_fiber_output_approx_forces_product_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_true_fiber_output_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_false_fiber_output_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_true_fiber_output_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y τ htrue hfalse htol

theorem coinwise_false_fiber_output_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y τ htrue hfalse htol

theorem coinwise_true_fiber_output_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_lowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_false_fiber_output_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_lowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_true_fiber_output_source_product_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_false_fiber_output_source_product_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_true_fiber_output_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_false_fiber_output_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_true_fiber_output_source_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceLowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_false_fiber_output_source_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceLowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_true_fiber_output_source_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceProduct_gt
      C E r y τ htrue hfalse htol

theorem coinwise_false_fiber_output_source_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceProduct_gt
      C E r y τ htrue hfalse htol

theorem coupled_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_coupled_nonconstant_on_condition
      C E F hcouple hpos hneg

theorem anticoupled_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_anticoupled_nonconstant_on_condition
      C E F hanti hpos hneg

theorem bool_to_any_recoding_distinguishing_fiber_zero_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_boolToAnyRecoding_fiber_distinguishes
      C E r y hdistinguish hpos hneg

theorem bool_to_any_recoding_output_zero_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconst : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_boolToAnyRecoding_nonconstant
      C E r hnonconst hpos hneg

theorem coinwise_true_fiber_output_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
      C E r y htrue hfalse hpos hneg

theorem coinwise_false_fiber_output_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
      C E r y htrue hfalse hpos hneg

theorem coinwise_true_fiber_source_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
      C E r y htrue hfalse hpos hneg

theorem coinwise_false_fiber_source_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
      C E r y htrue hfalse hpos hneg

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
