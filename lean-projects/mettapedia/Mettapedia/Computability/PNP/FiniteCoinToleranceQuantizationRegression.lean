import Mettapedia.Computability.PNP.FiniteCoinToleranceQuantization

/-!
# Regression checks for finite-coin tolerance quantization

These wrappers pin the threshold consequences of the scaled finite-coin defect
formula: below one `|Coin|` block of tolerance, approximate output independence
is exact balanced-fiber erasure.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinToleranceQuantizationRegression

open Mettapedia.Computability.PNP

theorem card_le_scaled_imbalance_of_ne_zero_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α)
    (hne : finiteCoinFiberImbalance r y ≠ 0) :
    Fintype.card Coin ≤
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  exact finiteCoin_card_le_scaled_fiberImbalance_of_ne_zero r y hne

theorem fiber_imbalance_zero_of_scaled_below_card_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) {τ : Nat}
    (hle : Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ)
    (hlt : τ < Fintype.card Coin) :
    finiteCoinFiberImbalance r y = 0 := by
  exact finiteCoinFiberImbalance_eq_zero_of_scaled_le_of_lt_card r y hle hlt

theorem fiber_balanced_of_scaled_below_card_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) {τ : Nat}
    (hle : Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ)
    (hlt : τ < Fintype.card Coin) :
    coinTrueFiberCount r y = coinFalseFiberCount r y := by
  exact finiteCoinFiberBalanced_of_scaled_fiberImbalance_le_of_lt_card
    r y hle hlt

theorem fiber_balanced_of_output_tolerance_below_card_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ)
    (hlt : τ < Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_card
    r happrox hlt

theorem output_tolerance_below_card_iff_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_lt_card_iff_fiberBalanced
    r hlt

theorem fiber_balanced_of_output_defect_below_card_regression
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α)
    (hlt :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) < Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_outputDefect_lt_card r hlt

theorem card_le_output_defect_of_not_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α)
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    Fintype.card Coin ≤
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  exact card_le_outputDefect_of_not_finiteCoinRecodingFiberBalanced r hnot

theorem output_defect_below_card_iff_fiber_balanced_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) < Fintype.card Coin ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact countIndependentWithinOutputDefect_lt_card_iff_fiberBalanced r

end Mettapedia.Computability.PNP.FiniteCoinToleranceQuantizationRegression
