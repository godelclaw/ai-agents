import Mettapedia.Computability.PNP.FiniteCoinSourceErasureFoundation

/-!
# Regression checks for finite-coin source erasure

These wrappers pin the grassroots interface that converts balanced finite-coin
fibers into source erasure facts about output predicates and Boolean decoders.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinSourceErasureFoundationRegression

open Mettapedia.Computability.PNP

theorem predicate_erasing_iff_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing r

theorem predicate_erasing_of_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_of_fiberBalanced r hbal

theorem fiber_balanced_of_predicate_erasing_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_outputPredicateErasing r herase

theorem predicate_true_advantage_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputPredicate_trueCount_gt_falseCount
    r P hgt

theorem predicate_false_advantage_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputPredicate_falseCount_gt_trueCount
    r P hgt

theorem predicate_separation_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputPredicate_separates
    r P htrue hfalse

theorem source_ranges_separated_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hsep : FiniteCoinSourceRangesSeparated r) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_sourceRangesSeparated r hsep

theorem decoder_half_accurate_of_predicate_erasing_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (herase : FiniteCoinOutputPredicateErasing r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  exact finiteCoinOutputDecoderHalfAccurate_of_outputPredicateErasing r decode herase

theorem decoder_half_accurate_of_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  exact finiteCoinOutputDecoderHalfAccurate_of_fiberBalanced r decode hbal

theorem decoder_better_than_half_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin < finiteCoinOutputDecoderCorrectCount r decode) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputDecoder_correctCount_gt_card
    r decode hgt

theorem decoder_recovery_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputDecoder_recovers
    r decode htrue hfalse

theorem output_source_recovering_of_source_ranges_separated_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hsep : FiniteCoinSourceRangesSeparated r) :
    FiniteCoinOutputSourceRecovering r := by
  exact finiteCoinOutputSourceRecovering_of_sourceRangesSeparated r hsep

theorem output_source_recovering_refutes_erasing_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α)
    (hrec : FiniteCoinOutputSourceRecovering r) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputSourceRecovering r hrec

end Mettapedia.Computability.PNP.FiniteCoinSourceErasureFoundationRegression
