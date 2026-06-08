import Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerExactCancellation
import Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstructionRegression

/-!
# Regression checks for exact dithered quantizer cancellation

These wrappers pin the exact zero-tolerance boundary for independent finite
dither: every dithered quantizer bucket must have zero total signed bias on the
expanded `(output, seed)` support.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerExactCancellationRegression

open Mettapedia.Computability.PNP
open Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstructionRegression

theorem constant_dithered_quantizer_exact_cancellation_regression :
    ∀ z : Unit,
      (∑ yd ∈ finiteOutputPreimageFiber
          (fun yd : Bool × Bool =>
            constantDitheredQuantizer
              (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yd.1, yd.2)) z,
        finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yd.1) = 0 := by
  exact
    (countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
      boolCoinAsymmetricRecoding constantDitheredQuantizer).mp
      bool_coin_asymmetric_recoding_with_dither_constant_quantized_tolerance_zero_regression

theorem constant_dithered_quantizer_observed_bucket_counts_regression :
    ∀ z : Unit,
      finiteEventCount (Bool × Bool)
          (fun cd =>
            constantDitheredQuantizer
              (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding
                (boolCoinAsymmetricRecoding true cd.1), cd.2) = z) =
        finiteEventCount (Bool × Bool)
          (fun cd =>
            constantDitheredQuantizer
              (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding
                (boolCoinAsymmetricRecoding false cd.1), cd.2) = z) := by
  exact
    (countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_observedBucketCount_eq
      boolCoinAsymmetricRecoding constantDitheredQuantizer).mp
      bool_coin_asymmetric_recoding_with_dither_constant_quantized_tolerance_zero_regression

theorem nonnegative_bias_with_seed_quantizer_bool_coin_asymmetric_bucket_sum_regression :
    (∑ yd ∈ finiteOutputPreimageFiber
        (fun yd : Bool × Bool =>
          nonnegativeBiasWithSeedQuantizer
            (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yd.1, yd.2))
        (true, false),
      finiteCoinSignedFiberBias boolCoinAsymmetricRecoding yd.1) = 1 := by
  decide

theorem nonnegative_bias_with_seed_quantizer_not_tolerance_zero_regression :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Bool × Bool))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Bool × Bool))
      (finiteCoinOutput
        (finiteCoinSignedBiasDitheredQuantizedRecoding
          boolCoinAsymmetricRecoding nonnegativeBiasWithSeedQuantizer)) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_of_exists_nonzero_sum_signedFiberBias_preimage
      boolCoinAsymmetricRecoding nonnegativeBiasWithSeedQuantizer
  refine ⟨(true, false), ?_⟩
  rw [nonnegative_bias_with_seed_quantizer_bool_coin_asymmetric_bucket_sum_regression]
  norm_num

theorem nonnegative_bias_with_seed_quantizer_not_observed_bucket_counts_regression :
    ¬ ∀ z : Bool × Bool,
      finiteEventCount (Bool × Bool)
          (fun cd =>
            nonnegativeBiasWithSeedQuantizer
              (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding
                (boolCoinAsymmetricRecoding true cd.1), cd.2) = z) =
        finiteEventCount (Bool × Bool)
          (fun cd =>
            nonnegativeBiasWithSeedQuantizer
              (finiteCoinSignedFiberBias boolCoinAsymmetricRecoding
                (boolCoinAsymmetricRecoding false cd.1), cd.2) = z) := by
  intro hcounts
  exact
    nonnegative_bias_with_seed_quantizer_not_tolerance_zero_regression
      ((countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_observedBucketCount_eq
        boolCoinAsymmetricRecoding nonnegativeBiasWithSeedQuantizer).mpr hcounts)

end Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerExactCancellationRegression
