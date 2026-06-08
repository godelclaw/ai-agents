import Mettapedia.Computability.PNP.FiniteCoinPostprocessingImprovementObstruction

/-!
# Regression checks for finite-coin postprocessing improvement obstruction

These wrappers pin the strict-improvement collision theorems and one concrete
two-coin collapse canary.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingImprovementObstructionRegression

open Mettapedia.Computability.PNP

theorem observed_injective_of_no_observed_output_collision_regression
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (hnone :
      ¬ ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
        r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2)) :
    ∀ b1 c1 b2 c2,
      g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
  exact observedInjective_of_no_observedOutput_collision r g hnone

theorem observed_output_collision_of_postcompose_tolerance_not_tolerance_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact exists_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
    r g τ hpost hnot

theorem postprocessed_fiber_card_gt_one_of_postcompose_tolerance_not_tolerance_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ z : β, 1 < (finiteOutputPreimageFiber g z).card := by
  exact exists_postprocessedFiber_card_gt_one_of_postcompose_tolerance_of_not_tolerance
    r g τ hpost hnot

theorem observed_output_collision_of_postcompose_output_defect_lt_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact exists_observedOutput_collision_of_postcompose_outputDefect_lt r g hlt

theorem postprocessed_fiber_card_gt_one_of_postcompose_output_defect_lt_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ z : β, 1 < (finiteOutputPreimageFiber g z).card := by
  exact exists_postprocessedFiber_card_gt_one_of_postcompose_outputDefect_lt
    r g hlt

def boolCoinAsymmetricRecoding : Bool → Bool → Bool
  | true, _ => true
  | false, c => c

def boolToUnitCollapse : Bool → Unit :=
  fun _ => ()

theorem bool_coin_asymmetric_recoding_collapsed_tolerance_one_regression :
    CountIndependentWithinToleranceOutput (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput
        (fun b c => boolToUnitCollapse (boolCoinAsymmetricRecoding b c))) 1 := by
  rw [countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le]
  intro z
  fin_cases z
  norm_num [finiteCoinOutput, boolToUnitCollapse, boolCoinAsymmetricRecoding,
    finiteCoinFiberImbalance, coinTrueFiberCount, coinFalseFiberCount]

theorem bool_coin_asymmetric_recoding_not_tolerance_one_regression :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput boolCoinAsymmetricRecoding) 1 := by
  intro h
  have htrue :=
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      boolCoinAsymmetricRecoding 1).mp h true
  have hcoinTrue : coinTrueFiberCount boolCoinAsymmetricRecoding true = 2 := by
    simp [coinTrueFiberCount, boolCoinAsymmetricRecoding, finiteEventCount]
  have hcoinFalse : coinFalseFiberCount boolCoinAsymmetricRecoding true = 1 := by
    simpa [coinFalseFiberCount, boolCoinAsymmetricRecoding] using
      (finiteEventCount_eq_self (α := Bool) true)
  have himb : finiteCoinFiberImbalance boolCoinAsymmetricRecoding true = 1 := by
    rw [finiteCoinFiberImbalance, hcoinTrue, hcoinFalse]
    norm_num
  have hbad : 2 * finiteCoinFiberImbalance boolCoinAsymmetricRecoding true ≤ 1 := by
    simpa using htrue
  rw [himb] at hbad
  omega

theorem bool_coin_asymmetric_recoding_collapsed_collision_regression :
    ∃ b1 : Bool, ∃ c1 : Bool, ∃ b2 : Bool, ∃ c2 : Bool,
      boolCoinAsymmetricRecoding b1 c1 ≠ boolCoinAsymmetricRecoding b2 c2 ∧
        boolToUnitCollapse (boolCoinAsymmetricRecoding b1 c1) =
          boolToUnitCollapse (boolCoinAsymmetricRecoding b2 c2) := by
  exact
    exists_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding boolToUnitCollapse 1
      bool_coin_asymmetric_recoding_collapsed_tolerance_one_regression
      bool_coin_asymmetric_recoding_not_tolerance_one_regression

theorem bool_coin_asymmetric_recoding_collapsed_fiber_card_gt_one_regression :
    ∃ z : Unit, 1 < (finiteOutputPreimageFiber boolToUnitCollapse z).card := by
  exact
    exists_postprocessedFiber_card_gt_one_of_postcompose_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding boolToUnitCollapse 1
      bool_coin_asymmetric_recoding_collapsed_tolerance_one_regression
      bool_coin_asymmetric_recoding_not_tolerance_one_regression

theorem bool_coin_asymmetric_recoding_collapsed_output_defect_lt_regression :
    countIndependentWithinOutputDefect (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput
        (fun b c => boolToUnitCollapse (boolCoinAsymmetricRecoding b c))) <
    countIndependentWithinOutputDefect (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput boolCoinAsymmetricRecoding) := by
  have hpost_le :
      countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (fun b c => boolToUnitCollapse (boolCoinAsymmetricRecoding b c))) ≤ 1 := by
    exact
      (countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Bool => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (fun b c => boolToUnitCollapse (boolCoinAsymmetricRecoding b c))) 1).mp
        bool_coin_asymmetric_recoding_collapsed_tolerance_one_regression
  have horig_not_le :
      ¬ countIndependentWithinOutputDefect (Ω := Bool × Bool)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Bool))
          (finiteCoinOutput boolCoinAsymmetricRecoding) ≤ 1 := by
    intro hle
    exact bool_coin_asymmetric_recoding_not_tolerance_one_regression
      ((countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Bool => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput boolCoinAsymmetricRecoding) 1).mpr hle)
  have horig_lt :
      1 <
        countIndependentWithinOutputDefect (Ω := Bool × Bool)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Bool))
          (finiteCoinOutput boolCoinAsymmetricRecoding) :=
    Nat.lt_of_not_ge horig_not_le
  exact lt_of_le_of_lt hpost_le horig_lt

theorem bool_coin_asymmetric_recoding_collapsed_output_defect_collision_regression :
    ∃ b1 : Bool, ∃ c1 : Bool, ∃ b2 : Bool, ∃ c2 : Bool,
      boolCoinAsymmetricRecoding b1 c1 ≠ boolCoinAsymmetricRecoding b2 c2 ∧
        boolToUnitCollapse (boolCoinAsymmetricRecoding b1 c1) =
          boolToUnitCollapse (boolCoinAsymmetricRecoding b2 c2) := by
  exact
    exists_observedOutput_collision_of_postcompose_outputDefect_lt
      boolCoinAsymmetricRecoding boolToUnitCollapse
      bool_coin_asymmetric_recoding_collapsed_output_defect_lt_regression

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingImprovementObstructionRegression
