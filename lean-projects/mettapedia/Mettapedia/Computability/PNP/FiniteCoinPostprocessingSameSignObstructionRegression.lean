import Mettapedia.Computability.PNP.FiniteCoinPostprocessingSameSignObstruction

/-!
# Regression checks for same-sign finite-coin postprocessing obstruction

These wrappers pin the mixed-sign cancellation obstruction for deterministic
finite-coin postprocessing improvements.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingSameSignObstructionRegression

open Mettapedia.Computability.PNP

theorem fiber_imbalance_eq_natAbs_signed_bias_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    finiteCoinFiberImbalance r y = Int.natAbs (finiteCoinSignedFiberBias r y) := by
  exact finiteCoinFiberImbalance_eq_natAbs_signedFiberBias r y

theorem signed_bias_one_sided_of_no_opposite_sign_collision_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hnone :
      ¬ ∃ yPos yNeg : α,
        g yPos = g yNeg ∧
          0 < finiteCoinSignedFiberBias r yPos ∧
            finiteCoinSignedFiberBias r yNeg < 0) :
    finiteOutputFiberSignedBiasOneSided r g := by
  exact
    finiteOutputFiberSignedBiasOneSided_of_no_oppositeSignObservedOutputCollision
      r g hnone

theorem output_defect_le_of_signed_bias_one_sided_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hcoh : finiteOutputFiberSignedBiasOneSided r g) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) ≤
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) := by
  exact
    countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
      r g hcoh

theorem opposite_sign_collision_of_postcompose_output_defect_lt_regression
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
    ∃ yPos yNeg : α,
      g yPos = g yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  exact
    exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
      r g hlt

theorem opposite_sign_collision_of_postcompose_tolerance_not_tolerance_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
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
    ∃ yPos yNeg : α,
      g yPos = g yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  exact
    exists_oppositeSign_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
      r g τ hpost hnot

def boolCoinSameSignSplit : Bool → Bool → Bool × Bool
  | true, c => (true, c)
  | false, _ => (false, false)

def firstCoordinateCollapse : Bool × Bool → Bool :=
  Prod.fst

theorem bool_coin_same_sign_split_no_opposite_sign_collision_regression :
    ¬ ∃ yPos yNeg : Bool × Bool,
      firstCoordinateCollapse yPos = firstCoordinateCollapse yNeg ∧
        0 < finiteCoinSignedFiberBias boolCoinSameSignSplit yPos ∧
          finiteCoinSignedFiberBias boolCoinSameSignSplit yNeg < 0 := by
  intro h
  rcases h with ⟨⟨bp, cp⟩, ⟨bn, cn⟩, hEq, hPos, hNeg⟩
  cases bp <;> cases cp <;> cases bn <;> cases cn <;>
    all_goals
      simp [firstCoordinateCollapse, boolCoinSameSignSplit,
        finiteCoinSignedFiberBias, coinTrueFiberCount, coinFalseFiberCount] at hEq hPos hNeg
      try omega

theorem bool_coin_same_sign_split_signed_bias_one_sided_regression :
    finiteOutputFiberSignedBiasOneSided boolCoinSameSignSplit
      firstCoordinateCollapse := by
  exact
    finiteOutputFiberSignedBiasOneSided_of_no_oppositeSignObservedOutputCollision
      boolCoinSameSignSplit firstCoordinateCollapse
      bool_coin_same_sign_split_no_opposite_sign_collision_regression

theorem bool_coin_same_sign_split_not_output_defect_lt_regression :
    ¬ countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (fun b c => firstCoordinateCollapse (boolCoinSameSignSplit b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput boolCoinSameSignSplit) := by
  exact Nat.not_lt_of_ge
    (countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
      boolCoinSameSignSplit firstCoordinateCollapse
      bool_coin_same_sign_split_signed_bias_one_sided_regression)

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

theorem bool_coin_asymmetric_recoding_opposite_sign_tolerance_collision_regression :
    ∃ yPos yNeg : Bool,
      boolToUnitCollapse yPos = boolToUnitCollapse yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos ∧
          finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg < 0 := by
  exact
    exists_oppositeSign_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding boolToUnitCollapse 1
      bool_coin_asymmetric_recoding_collapsed_tolerance_one_regression
      bool_coin_asymmetric_recoding_not_tolerance_one_regression

theorem bool_coin_asymmetric_recoding_opposite_sign_output_defect_collision_regression :
    ∃ yPos yNeg : Bool,
      boolToUnitCollapse yPos = boolToUnitCollapse yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos ∧
          finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg < 0 := by
  exact
    exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
      boolCoinAsymmetricRecoding boolToUnitCollapse
      bool_coin_asymmetric_recoding_collapsed_output_defect_lt_regression

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingSameSignObstructionRegression
