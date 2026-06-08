import Mettapedia.Computability.PNP.ApproximateDecorrelationObstruction
import Mettapedia.Computability.PNP.FiniteCoinSignedBiasDitheredQuantizerObstruction

/-!
# P vs NP grassroots: exact cancellation for dithered signed-bias quantizers

The approximate obstruction for finite public dither says that same-sign
buckets cannot help.  This file records the exact zero-tolerance boundary:
balanced output after dithered signed-bias quantization is equivalent to an
exact signed-bias cancellation identity in every quantizer bucket on the
enlarged `(output, seed)` support.

So independent dither does not merely require a mixed-sign collision.  At exact
tolerance zero, every quantizer bucket must satisfy a concrete integer
conservation law.
-/

namespace Mettapedia.Computability.PNP

/-- The signed bias of a dithered signed-bias quantizer output is the sum of the
underlying original signed biases over the corresponding `(output, seed)`
preimage fiber. -/
theorem finiteCoinSignedFiberBias_finiteCoinSignedBiasDitheredQuantizedRecoding_eq_sum_preimage
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) (z : β) :
    finiteCoinSignedFiberBias (finiteCoinSignedBiasDitheredQuantizedRecoding r q) z =
      ∑ yd ∈ finiteOutputPreimageFiber
          (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
        finiteCoinSignedFiberBias r yd.1 := by
  classical
  let g : α × Dither → β := fun yd => q (finiteCoinSignedFiberBias r yd.1, yd.2)
  calc
    finiteCoinSignedFiberBias (finiteCoinSignedBiasDitheredQuantizedRecoding r q) z =
        finiteCoinSignedFiberBias (fun b cd => g ((finiteCoinOutputWithDither r) b cd)) z := by
          rfl
    _ =
        ∑ yd ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias (finiteCoinOutputWithDither r) yd := by
            simpa [g] using
              (finiteCoinSignedFiberBias_postcompose_eq_sum_preimage
                (r := finiteCoinOutputWithDither r) (g := g) z)
    _ =
        ∑ yd ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r yd.1 := by
            refine Finset.sum_congr rfl ?_
            intro yd _hyd
            rcases yd with ⟨y, d⟩
            simp [finiteCoinSignedFiberBias_outputWithDither]

/-- Exact balance after dithered signed-bias quantization is equivalent to exact
signed-bias cancellation in every dithered quantizer bucket. -/
theorem finiteCoinRecodingFiberBalanced_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) :
    FiniteCoinRecodingFiberBalanced (finiteCoinSignedBiasDitheredQuantizedRecoding r q) ↔
      ∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0 := by
  rw [finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
    (finiteCoinSignedBiasDitheredQuantizedRecoding r q)]
  constructor <;> intro h z
  · have hz := h z
    rwa [finiteCoinSignedFiberBias_finiteCoinSignedBiasDitheredQuantizedRecoding_eq_sum_preimage] at hz
  · rw [finiteCoinSignedFiberBias_finiteCoinSignedBiasDitheredQuantizedRecoding_eq_sum_preimage]
    exact h z

/-- The exact signed-bias cancellation law for dithered quantization is exactly
the generic retained-side witness-count equality criterion on the enlarged
`(output, seed)` surface. -/
theorem finiteCoinSignedBiasDitheredQuantizedRecoding_exactCancellation_iff_observedBucketCount_eq
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) :
    (∀ z : β,
      (∑ yd ∈ finiteOutputPreimageFiber
          (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
        finiteCoinSignedFiberBias r yd.1) = 0) ↔
      ∀ z : β,
        finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r true cd.1), cd.2) = z) =
          finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r false cd.1), cd.2) = z) := by
  calc
    (∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0) ↔
      FiniteCoinRecodingFiberBalanced
        (finiteCoinSignedBiasDitheredQuantizedRecoding r q) := by
          exact
            (finiteCoinRecodingFiberBalanced_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
              r q).symm
    _ ↔
      ∀ z : β,
        finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r true cd.1), cd.2) = z) =
          finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r false cd.1), cd.2) = z) := by
            simpa [finiteCoinSignedBiasDitheredQuantizedRecoding] using
              (finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
                (r := fun b (cd : Coin × Dither) => r b cd.1)
                (side := fun cd : Coin × Dither => cd.2)
                (post := fun yd : α × Dither =>
                  q (finiteCoinSignedFiberBias r yd.1, yd.2)))

/-- Zero-tolerance output independence for a dithered signed-bias quantizer is
exactly the same per-bucket signed-bias cancellation law. -/
theorem countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) :
    CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) 0 ↔
      ∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0 := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) 0 ↔
      FiniteCoinRecodingFiberBalanced (finiteCoinSignedBiasDitheredQuantizedRecoding r q) := by
          exact
            (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
              (finiteCoinSignedBiasDitheredQuantizedRecoding r q)).symm
    _ ↔
      ∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0 :=
        finiteCoinRecodingFiberBalanced_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
          r q

/-- Route-facing zero-tolerance form: dithered signed-bias quantization can
decorrelate exactly only when every observed quantizer bucket has matching
true-side and false-side witness counts on the expanded `(coin, seed)` domain. -/
theorem countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_observedBucketCount_eq
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) :
    CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) 0 ↔
      ∀ z : β,
        finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r true cd.1), cd.2) = z) =
          finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r false cd.1), cd.2) = z) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) 0 ↔
      ∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0 :=
        countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
          r q
    _ ↔
      ∀ z : β,
        finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r true cd.1), cd.2) = z) =
          finiteEventCount (Coin × Dither)
            (fun cd =>
              q (finiteCoinSignedFiberBias r (r false cd.1), cd.2) = z) :=
        finiteCoinSignedBiasDitheredQuantizedRecoding_exactCancellation_iff_observedBucketCount_eq
          r q

/-- A single dithered quantizer bucket with nonzero total signed bias blocks
zero-tolerance output independence. -/
theorem not_countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_of_exists_nonzero_sum_signedFiberBias_preimage
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β)
    (hex :
      ∃ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) ≠ 0) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) 0 := by
  intro hzero
  have hall :
      ∀ z : β,
        (∑ yd ∈ finiteOutputPreimageFiber
            (fun yd : α × Dither => q (finiteCoinSignedFiberBias r yd.1, yd.2)) z,
          finiteCoinSignedFiberBias r yd.1) = 0 :=
    (countIndependentWithinToleranceOutput_zero_finiteCoinSignedBiasDitheredQuantizedRecoding_iff_forall_sum_signedFiberBias_preimage_eq_zero
      r q).mp hzero
  rcases hex with ⟨z, hz⟩
  exact hz (hall z)

end Mettapedia.Computability.PNP
