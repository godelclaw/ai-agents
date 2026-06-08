import Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstruction

/-!
# Regression checks for dithered signed-bias quantizer obstruction

These wrappers pin the finite-coin statement that independent finite dither
does not rescue one-sided quantization of the signed boundary bias.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstructionRegression

open Mettapedia.Computability.PNP

def nonnegativeBiasWithSeedQuantizer : Int × Bool → Bool × Bool :=
  fun sd => (decide (0 ≤ sd.1), sd.2)

theorem nonnegative_bias_with_seed_quantizer_one_sided_regression :
    finiteCoinSignedBiasDitheredQuantizerOneSided
      nonnegativeBiasWithSeedQuantizer := by
  intro z
  rcases z with ⟨sign, d⟩
  cases sign
  · right
    intro s d' hs
    by_cases h : 0 ≤ s
    · simp [nonnegativeBiasWithSeedQuantizer, h] at hs
    · exact le_of_lt (lt_of_not_ge h)
  · left
    intro s d' hs
    by_cases h : 0 ≤ s
    · exact h
    · simp [nonnegativeBiasWithSeedQuantizer, h] at hs

def boolCoinSameSignSplit : Bool → Bool → Bool × Bool
  | true, c => (true, c)
  | false, _ => (false, false)

theorem bool_coin_same_sign_split_dithered_quantized_not_output_defect_lt_regression :
    ¬ countIndependentWithinOutputDefect (Ω := Bool × (Bool × Bool))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool × Bool))
        (finiteCoinOutput
          (finiteCoinSignedBiasDitheredQuantizedRecoding
            boolCoinSameSignSplit nonnegativeBiasWithSeedQuantizer)) <
      countIndependentWithinOutputDefect (Ω := Bool × (Bool × Bool))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Bool × Bool))
        (finiteCoinOutput
          (finiteCoinOutputWithDither boolCoinSameSignSplit)) := by
  exact Nat.not_lt_of_ge
    (countIndependentWithinOutputDefect_finiteCoinOutputWithDither_le_of_finiteCoinSignedBiasDitheredQuantizerOneSided
      boolCoinSameSignSplit nonnegativeBiasWithSeedQuantizer
      nonnegative_bias_with_seed_quantizer_one_sided_regression)

def boolCoinAsymmetricRecoding : Bool → Bool → Bool
  | true, _ => true
  | false, c => c

def constantDitheredQuantizer : Int × Bool → Unit :=
  fun _ => ()

theorem bool_coin_asymmetric_recoding_with_dither_constant_quantized_tolerance_zero_regression :
    CountIndependentWithinToleranceOutput (Ω := Bool × (Bool × Bool))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool × Bool))
      (finiteCoinOutput
        (finiteCoinSignedBiasDitheredQuantizedRecoding
          boolCoinAsymmetricRecoding constantDitheredQuantizer)) 0 := by
  have hbal :
      FiniteCoinRecodingFiberBalanced
        (finiteCoinSignedBiasDitheredQuantizedRecoding
          boolCoinAsymmetricRecoding constantDitheredQuantizer) := by
    simpa [finiteCoinSignedBiasDitheredQuantizedRecoding, constantDitheredQuantizer] using
      (finiteCoinRecodingFiberBalanced_constant
        (Coin := Bool × Bool) (β := Unit) ())
  exact
    (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
      (finiteCoinSignedBiasDitheredQuantizedRecoding
        boolCoinAsymmetricRecoding constantDitheredQuantizer)).mp hbal

theorem bool_coin_asymmetric_recoding_with_dither_not_tolerance_zero_regression :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Bool × Bool))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool × Bool))
      (finiteCoinOutput
        (finiteCoinOutputWithDither boolCoinAsymmetricRecoding)) 0 := by
  intro h
  have hbal :
      FiniteCoinRecodingFiberBalanced
        (finiteCoinOutputWithDither boolCoinAsymmetricRecoding) :=
    (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
      (finiteCoinOutputWithDither boolCoinAsymmetricRecoding)).mpr h
  have hbias :
      finiteCoinSignedFiberBias
          (finiteCoinOutputWithDither boolCoinAsymmetricRecoding)
          (true, false) = 0 :=
    (finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
      (finiteCoinOutputWithDither boolCoinAsymmetricRecoding)).mp hbal (true, false)
  have hcoinTrue : coinTrueFiberCount boolCoinAsymmetricRecoding true = 2 := by
    simp [coinTrueFiberCount, boolCoinAsymmetricRecoding, finiteEventCount]
  have hcoinFalse : coinFalseFiberCount boolCoinAsymmetricRecoding true = 1 := by
    simpa [coinFalseFiberCount, boolCoinAsymmetricRecoding] using
      (finiteEventCount_eq_self (α := Bool) true)
  have hpos : 0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding true := by
    rw [finiteCoinSignedFiberBias, hcoinTrue, hcoinFalse]
    norm_num
  rw [finiteCoinSignedFiberBias_outputWithDither
      (r := boolCoinAsymmetricRecoding) (y := true) (d := false)] at hbias
  rw [hbias] at hpos
  exact lt_irrefl _ hpos

theorem constant_dithered_quantizer_not_one_sided_tolerance_zero_regression :
    ¬ finiteCoinSignedBiasDitheredQuantizerOneSided constantDitheredQuantizer := by
  exact
    not_finiteCoinSignedBiasDitheredQuantizerOneSided_of_quantizedOutput_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding constantDitheredQuantizer 0
      bool_coin_asymmetric_recoding_with_dither_constant_quantized_tolerance_zero_regression
      bool_coin_asymmetric_recoding_with_dither_not_tolerance_zero_regression

theorem constant_dithered_quantizer_opposite_sign_collision_tolerance_zero_regression :
    ∃ yPos yNeg : Bool, ∃ dPos dNeg : Bool,
      constantDitheredQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos, dPos) =
        constantDitheredQuantizer (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg, dNeg) ∧
        0 < finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yPos ∧
          finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yNeg < 0 := by
  exact
    exists_oppositeSign_ditheredQuantizerCollision_of_quantizedOutput_tolerance_of_not_tolerance
      boolCoinAsymmetricRecoding constantDitheredQuantizer 0
      bool_coin_asymmetric_recoding_with_dither_constant_quantized_tolerance_zero_regression
      bool_coin_asymmetric_recoding_with_dither_not_tolerance_zero_regression

end Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstructionRegression
