import Mettapedia.Computability.PNP.FiniteCoinIndependenceBridge

/-!
# Regression checks for the finite-coin independence bridge

These wrappers pin the bridge between finite-coin predicate erasure and exact
finite-count independence on the two-sided sample space `Bool × Coin`.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinIndependenceBridgeRegression

open Mettapedia.Computability.PNP

theorem source_true_count_regression
    {Coin : Type*} [Fintype Coin] :
    finiteEventCount (Bool × Coin) (finiteCoinSourceTrue (Coin := Coin)) =
      Fintype.card Coin := by
  exact finiteCoinSourceTrue_count

theorem output_predicate_count_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    finiteEventCount (Bool × Coin) (fun ω => P (finiteCoinOutput r ω)) =
      finiteEventCount Coin (fun c => P (r true c)) +
        finiteEventCount Coin (fun c => P (r false c)) := by
  exact finiteCoinOutputPredicate_count r P

theorem predicate_neutral_iff_source_independent_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    finiteCoinOutputPredicateNeutral r P ↔
      CountIndependentWithin (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => P (finiteCoinOutput r ω)) := by
  exact finiteCoinOutputPredicateNeutral_iff_countIndependentWithin_trueSource_outputPredicate
    r P

theorem predicate_erasing_iff_all_source_independent_regression
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) :
    FiniteCoinOutputPredicateErasing r ↔
      ∀ P : α → Prop, [DecidablePred P] →
        CountIndependentWithin (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (fun ω => P (finiteCoinOutput r ω)) := by
  exact finiteCoinOutputPredicateErasing_iff_forall_countIndependentWithin_trueSource_outputPredicate
    r

theorem fiber_balanced_iff_zero_tolerance_output_independence_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) 0 := by
  exact finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero r

theorem fiber_balanced_iff_zero_output_defect_regression
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) = 0 := by
  exact finiteCoinRecodingFiberBalanced_iff_countIndependentWithinOutputDefect_eq_zero r

end Mettapedia.Computability.PNP.FiniteCoinIndependenceBridgeRegression
