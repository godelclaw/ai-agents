import Mettapedia.Computability.PNP.FiniteCoinDefectFormula

/-!
# Regression checks for finite-coin output defect formulas

These wrappers pin the exact quantitative bridge between finite-count
source/output defects on `Bool × Coin` and true/false coin-fiber imbalance.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinDefectFormulaRegression

open Mettapedia.Computability.PNP

theorem fiber_imbalance_zero_iff_balanced_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    finiteCoinFiberImbalance r y = 0 ↔
      coinTrueFiberCount r y = coinFalseFiberCount r y := by
  exact finiteCoinFiberImbalance_eq_zero_iff r y

theorem forward_gap_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin *
        (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  exact countIndependentWithinForwardGap_finiteCoinOutput_fiber r y

theorem backward_gap_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin *
        (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  exact countIndependentWithinBackwardGap_finiteCoinOutput_fiber r y

theorem fiber_defect_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  exact countIndependentWithinDefect_finiteCoinOutput_fiber r y

theorem output_tolerance_iff_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (τ : Nat) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) τ ↔
      ∀ y : α, Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
    r τ

theorem output_defect_sup_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) =
      (Finset.univ : Finset α).sup
        (fun y => Fintype.card Coin * finiteCoinFiberImbalance r y) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_eq_sup_scaled_fiberImbalance r

theorem fiber_balanced_iff_all_imbalances_zero_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinFiberImbalance r y = 0 := by
  exact finiteCoinRecodingFiberBalanced_iff_forall_fiberImbalance_eq_zero r

end Mettapedia.Computability.PNP.FiniteCoinDefectFormulaRegression
