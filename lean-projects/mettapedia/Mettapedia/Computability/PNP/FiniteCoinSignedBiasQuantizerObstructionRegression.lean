import Mettapedia.Computability.PNP.FiniteCoinSignedBiasQuantizerObstruction

/-!
# Regression checks for signed-bias quantizer obstruction

These wrappers pin the finite-coin statement that one-sided quantizers of the
signed boundary bias cannot improve approximate source/output independence.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinSignedBiasQuantizerObstructionRegression

open Mettapedia.Computability.PNP

theorem signed_bias_quantizer_one_sided_regression
    {β : Type*} (q : Int → β) :
    finiteCoinSignedBiasQuantizerOneSided q →
      finiteCoinSignedBiasQuantizerOneSided q := by
  intro h
  exact h

def nonnegativeBiasQuantizer : Int → Bool :=
  fun s => decide (0 ≤ s)

theorem nonnegative_bias_quantizer_one_sided_regression :
    finiteCoinSignedBiasQuantizerOneSided nonnegativeBiasQuantizer := by
  intro z
  cases z
  · right
    intro s hs
    by_cases h : 0 ≤ s
    · simp [nonnegativeBiasQuantizer, h] at hs
    · exact le_of_lt (lt_of_not_ge h)
  · left
    intro s hs
    by_cases h : 0 ≤ s
    · exact h
    · simp [nonnegativeBiasQuantizer, h] at hs

def boolCoinSameSignSplit : Bool → Bool → Bool × Bool
  | true, c => (true, c)
  | false, _ => (false, false)

def firstCoordinateCollapse : Bool × Bool → Bool :=
  Prod.fst

theorem bool_coin_same_sign_split_quantized_recoding_eq_first_coordinate_regression :
    finiteCoinSignedBiasQuantizedRecoding boolCoinSameSignSplit
        nonnegativeBiasQuantizer =
      fun b c => firstCoordinateCollapse (boolCoinSameSignSplit b c) := by
  funext b c
  cases b <;> cases c <;>
    norm_num [finiteCoinSignedBiasQuantizedRecoding, nonnegativeBiasQuantizer,
      boolCoinSameSignSplit, firstCoordinateCollapse, finiteCoinSignedFiberBias,
      coinTrueFiberCount, coinFalseFiberCount, finiteEventCount]

theorem bool_coin_same_sign_split_quantized_not_output_defect_lt_regression :
    ¬ countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (finiteCoinSignedBiasQuantizedRecoding boolCoinSameSignSplit
            nonnegativeBiasQuantizer)) <
      countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput boolCoinSameSignSplit) := by
  exact Nat.not_lt_of_ge
    (countIndependentWithinOutputDefect_finiteCoinOutput_le_of_finiteCoinSignedBiasQuantizerOneSided
      boolCoinSameSignSplit nonnegativeBiasQuantizer
      nonnegative_bias_quantizer_one_sided_regression)

def boolCoinAsymmetricRecoding : Bool → Bool → Bool
  | true, _ => true
  | false, c => c

def constantBiasQuantizer : Int → Unit :=
  fun _ => ()

theorem bool_coin_asymmetric_recoding_constant_quantized_tolerance_one_regression :
    CountIndependentWithinToleranceOutput (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput
        (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
          constantBiasQuantizer)) 1 := by
  have hbal :
      FiniteCoinRecodingFiberBalanced
        (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
          constantBiasQuantizer) := by
    simpa [finiteCoinSignedBiasQuantizedRecoding, constantBiasQuantizer] using
      (finiteCoinRecodingFiberBalanced_constant (Coin := Bool) (β := Unit) ())
  have hzero :
      CountIndependentWithinToleranceOutput (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
            constantBiasQuantizer)) 0 := by
    exact
      (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
        (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
          constantBiasQuantizer)).mp hbal
  exact countIndependentWithinToleranceOutput_mono
    (fun _ω : Bool × Bool => True)
    (finiteCoinSourceTrue (Coin := Bool))
    (finiteCoinOutput
      (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
        constantBiasQuantizer))
    (Nat.zero_le 1)
    hzero

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

theorem bool_coin_asymmetric_recoding_constant_quantized_output_defect_lt_regression :
    countIndependentWithinOutputDefect (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput
        (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
          constantBiasQuantizer)) <
    countIndependentWithinOutputDefect (Ω := Bool × Bool)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput boolCoinAsymmetricRecoding) := by
  have hpost_le :
      countIndependentWithinOutputDefect (Ω := Bool × Bool)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool))
        (finiteCoinOutput
          (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
            constantBiasQuantizer)) ≤ 1 :=
    (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Bool => True)
      (finiteCoinSourceTrue (Coin := Bool))
      (finiteCoinOutput
        (finiteCoinSignedBiasQuantizedRecoding boolCoinAsymmetricRecoding
          constantBiasQuantizer)) 1).mp
      bool_coin_asymmetric_recoding_constant_quantized_tolerance_one_regression
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

theorem constant_bias_quantizer_not_one_sided_output_defect_regression :
    ¬ finiteCoinSignedBiasQuantizerOneSided constantBiasQuantizer := by
  exact
    not_finiteCoinSignedBiasQuantizerOneSided_of_quantizedOutput_outputDefect_lt
      boolCoinAsymmetricRecoding constantBiasQuantizer
      bool_coin_asymmetric_recoding_constant_quantized_output_defect_lt_regression

theorem constant_bias_quantizer_not_one_sided_tolerance_regression :
    ¬ finiteCoinSignedBiasQuantizerOneSided constantBiasQuantizer := by
  exact
    not_finiteCoinSignedBiasQuantizerOneSided_of_quantizedOutput_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding constantBiasQuantizer 1
      bool_coin_asymmetric_recoding_constant_quantized_tolerance_one_regression
      bool_coin_asymmetric_recoding_not_tolerance_one_regression

theorem constant_bias_quantizer_opposite_sign_collision_output_defect_regression :
    ∃ yPos yNeg : Bool,
      constantBiasQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos) =
        constantBiasQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg) ∧
        yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos ∧
          finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg < 0 := by
  exact
    exists_oppositeSign_quantizerCollision_of_quantizedOutput_outputDefect_lt
      boolCoinAsymmetricRecoding constantBiasQuantizer
      bool_coin_asymmetric_recoding_constant_quantized_output_defect_lt_regression

theorem constant_bias_quantizer_opposite_sign_collision_tolerance_regression :
    ∃ yPos yNeg : Bool,
      constantBiasQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos) =
        constantBiasQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg) ∧
        yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos ∧
          finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg < 0 := by
  exact
    exists_oppositeSign_quantizerCollision_of_quantizedOutput_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding constantBiasQuantizer 1
      bool_coin_asymmetric_recoding_constant_quantized_tolerance_one_regression
      bool_coin_asymmetric_recoding_not_tolerance_one_regression

end Mettapedia.Computability.PNP.FiniteCoinSignedBiasQuantizerObstructionRegression
