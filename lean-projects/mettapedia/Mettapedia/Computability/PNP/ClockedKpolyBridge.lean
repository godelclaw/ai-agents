import Mettapedia.Computability.PNP.BitFamilyUniformSuccessBinary
import Mettapedia.Computability.PNP.ExactSwitchedFamily

/-!
# PNP clocked `Kpoly` bridge kernel

This file isolates the finite counting part of the clocked `Kpoly` bridge.
It does not assert that the manuscript's switched decoder is representable by
such a family.  Instead, it records what becomes available after that missing
realization theorem is supplied: a clocked `s`-bit decoder family has the same
finite-uniform ERM recovery guarantees as any `s`-bit encoded Boolean family.

The clock parameter is explicit bookkeeping.  The counting theorem depends on
the number of admissible program bits, while the separate manuscript burden is
to prove that the actual decoder is covered by this clocked family with the
claimed clock bound.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- A clocked Boolean decoder family with `s` admissible program bits.  The
clock is part of the interface but not part of the finite counting argument. -/
structure ClockedBitCodeFamily (Input : Type u) (s clock : ℕ) where
  decode : BitCode s → Input → Bool

namespace ClockedBitCodeFamily

variable {Input : Type u} {s clock : ℕ}

/-- Forget the clock and view a clocked family as an ordinary bit-encoded
classifier family. -/
def toBitEncodedClassifierFamily (F : ClockedBitCodeFamily Input s clock) :
    BitEncodedClassifierFamily Input s where
  decode := F.decode

/-- Equip an ordinary bit-encoded classifier family with an external clock
parameter.  The clock is bookkeeping; the decoder is unchanged. -/
def ofBitEncodedClassifierFamily
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s) :
    ClockedBitCodeFamily Input s clock where
  decode := F.decode

@[simp]
theorem toBitEncodedClassifierFamily_ofBitEncodedClassifierFamily
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s) :
    (ofBitEncodedClassifierFamily (Input := Input) (s := s) clock F).toBitEncodedClassifierFamily =
      F := by
  rfl

/-- A target is realized by a clocked bit-code family when some admissible
program code decodes to it. -/
def Realizes (F : ClockedBitCodeFamily Input s clock) (target : Input → Bool) : Prop :=
  ∃ code : BitCode s, F.decode code = target

/-- Realization by a clocked wrapper is exactly realization by the underlying
bit family. -/
theorem ofBitEncodedClassifierFamily_realizes_iff
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) :
    (ofBitEncodedClassifierFamily (Input := Input) (s := s) clock F).Realizes target ↔
      ∃ code : BitCode s, F.decode code = target := by
  rfl

/-- Exact ERM recovery rate for the underlying finite encoded family. -/
noncomputable def exactRecoveryRate [Fintype Input]
    (F : ClockedBitCodeFamily Input s clock) (target : Input → Bool) (m : ℕ) : ℚ :=
  F.toBitEncodedClassifierFamily.toEncodedFamily.exactRecoveryRate target m

/-- Non-deceptive sample rate for the underlying finite encoded family. -/
noncomputable def nondeceptiveRate [Fintype Input]
    (F : ClockedBitCodeFamily Input s clock) (target : Input → Bool) (m : ℕ) : ℚ :=
  F.toBitEncodedClassifierFamily.toEncodedFamily.nondeceptiveRate target m

/-- The ERM predictor selected by the underlying finite encoded family. -/
noncomputable def empiricalRiskPredictor
    (F : ClockedBitCodeFamily Input s clock) (sample : Sample Input Bool) : Input → Bool :=
  F.toBitEncodedClassifierFamily.empiricalRiskPredictor sample

/-- Clocking an ordinary bit family does not change its exact recovery rate. -/
theorem exactRecoveryRate_ofBitEncodedClassifierFamily
    [Fintype Input]
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) :
    (ofBitEncodedClassifierFamily (Input := Input) (s := s) clock F).exactRecoveryRate
        target m =
      F.toEncodedFamily.exactRecoveryRate target m := by
  rfl

/-- Clocking an ordinary bit family does not change its non-deceptive sample
rate. -/
theorem nondeceptiveRate_ofBitEncodedClassifierFamily
    [Fintype Input]
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) :
    (ofBitEncodedClassifierFamily (Input := Input) (s := s) clock F).nondeceptiveRate
        target m =
      F.toEncodedFamily.nondeceptiveRate target m := by
  rfl

/-- Clocking an ordinary bit family does not change its ERM predictor. -/
theorem empiricalRiskPredictor_ofBitEncodedClassifierFamily
    (clock : ℕ) (F : BitEncodedClassifierFamily Input s)
    (sample : Sample Input Bool) :
    (ofBitEncodedClassifierFamily (Input := Input) (s := s) clock F).empiricalRiskPredictor
        sample =
      F.empiricalRiskPredictor sample := by
  rfl

/-- The realized classifier class of a clocked `s`-bit family has size at most
`2^s`.  The clock contributes no extra hypotheses; it is an operational
constraint to be proved separately for the concrete decoder. -/
theorem card_realized_le_bitBudget (F : ClockedBitCodeFamily Input s clock) :
    Fintype.card
        (EncodedFamily.realized F.toBitEncodedClassifierFamily.toEncodedFamily) ≤ 2 ^ s := by
  exact F.toBitEncodedClassifierFamily.card_realized_le

/-- Generic finite-uniform non-deceptive-rate bound for a clocked `s`-bit
family. -/
theorem nondeceptiveRate_ge_one_sub_uniformMissRatio_pow [Fintype Input]
    [Nonempty Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow
      target m

/-- Positivity form of the clocked finite-uniform non-deceptive-rate bound. -/
theorem nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
    [Fintype Input] [Nonempty Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      target m hlt

/-- Pure finite-counting existence: below the bit-budget cardinality threshold,
some point sample is non-deceptive for the underlying clocked family. -/
theorem exists_nondeceptiveSample_of_bitBudget_bound_lt
    [Fintype Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ¬ F.toBitEncodedClassifierFamily.toEncodedFamily.IsDeceptiveSample target sample := by
  exact
    F.toBitEncodedClassifierFamily.exists_nondeceptiveSample_of_bitBudget_bound_lt
      target m hbound

/-- Pure finite-counting exact recovery: below the bit-budget cardinality
threshold, ERM over a clocked family exactly recovers any realized target on
some point sample. -/
theorem exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
    [Fintype Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (htarget : F.Realizes target)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  simpa [empiricalRiskPredictor, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
      target m htarget hbound

/-- Generic finite-uniform recovery bound for a clocked `s`-bit family. -/
theorem exactRecoveryRate_ge_one_sub_uniformMissRatio_pow [Fintype Input]
    [Nonempty Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (htarget : F.Realizes target) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow
      target m htarget

/-- Positivity form of the clocked finite-uniform recovery bound. -/
theorem exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
    [Fintype Input] [Nonempty Input]
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (htarget : F.Realizes target)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      target m htarget hlt

/-- Boolean-domain clocked non-deceptive-rate bound with the miss ratio
simplified to `1 / 2`. -/
theorem nondeceptiveRate_ge_one_sub_bool_bitBudget_pow
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_ge_one_sub_bool_bitBudget_pow
      target m

/-- Boolean-domain clocked recovery bound with the miss ratio simplified to
`1 / 2`. -/
theorem exactRecoveryRate_ge_one_sub_bool_bitBudget_pow
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m : ℕ)
    (htarget : F.Realizes target) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_ge_one_sub_bool_bitBudget_pow
      target m htarget

/-- If the Boolean sample length exceeds the bit budget by at least `k`, a
clocked `s`-bit family has non-deceptive sample rate at least
`1 - (1/2)^k` for every target. -/
theorem nondeceptiveRate_ge_one_sub_bool_margin_pow
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_ge_one_sub_bool_margin_pow
      target m k hskm

/-- If the Boolean sample length exceeds the bit budget by at least `k`, a
clocked `s`-bit family has exact ERM recovery rate at least
`1 - (1/2)^k` for every realized target. -/
theorem exactRecoveryRate_ge_one_sub_bool_margin_pow
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : F.Realizes target)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_ge_one_sub_bool_margin_pow
      target m k htarget hskm

/-- Boolean-domain non-deceptive-rate positivity from any positive sample
margin over the bit budget. -/
theorem nondeceptiveRate_pos_bool_of_positive_margin
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_pos_bool_of_positive_margin
      target m k hskm hk

/-- Boolean-domain positivity from any positive sample margin over the bit
budget. -/
theorem exactRecoveryRate_pos_bool_of_positive_margin
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : F.Realizes target)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_pos_bool_of_positive_margin
      target m k htarget hskm hk

/-- Boolean-domain non-deceptive-rate positivity from the concrete sample-size
inequality `s < m`. -/
theorem nondeceptiveRate_pos_bool_of_lt_sampleSize
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (hsm : s < m) :
    0 < F.nondeceptiveRate target m := by
  simpa [nondeceptiveRate, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.nondeceptiveRate_pos_bool_of_lt_sampleSize
      target hsm

/-- Boolean-domain non-deceptive sample existence from the concrete sample-size
inequality `s < m`. -/
theorem exists_bool_nondeceptiveSample_of_lt_sampleSize
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      ¬ F.toBitEncodedClassifierFamily.toEncodedFamily.IsDeceptiveSample target sample := by
  exact
    F.toBitEncodedClassifierFamily.exists_bool_nondeceptiveSample_of_lt_sampleSize
      target hsm

/-- Boolean-domain exact ERM recovery from the concrete sample-size inequality
`s < m`. -/
theorem exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (htarget : F.Realizes target)
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  simpa [empiricalRiskPredictor, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize
      target htarget hsm

/-- Boolean-domain positivity from the concrete sample-size inequality
`s < m`. -/
theorem exactRecoveryRate_pos_bool_of_lt_sampleSize
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (htarget : F.Realizes target)
    (hsm : s < m) :
    0 < F.exactRecoveryRate target m := by
  simpa [exactRecoveryRate, Realizes, toBitEncodedClassifierFamily] using
    F.toBitEncodedClassifierFamily.exactRecoveryRate_pos_bool_of_lt_sampleSize
      target htarget hsm

end ClockedBitCodeFamily

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v} {s clock : ℕ}

/-- Every predictor in `G` is realized by some admissible program of the
clocked `s`-bit family `F`. -/
def RealizedByClockedBitFamily
    (G : IndexedPredictorFamily Index Input)
    (F : ClockedBitCodeFamily Input s clock) : Prop :=
  ∀ i, F.Realizes (G.predict i)

/-- A clocked realization family immediately yields the corresponding exact
bit-budget theorem after forgetting the clock bookkeeping. -/
theorem hasBitBudget_of_realizedByClockedBitFamily
    {G : IndexedPredictorFamily Index Input}
    {F : ClockedBitCodeFamily Input s clock}
    (hreal : G.RealizedByClockedBitFamily F) :
    G.HasBitBudget s := by
  refine ⟨F.toBitEncodedClassifierFamily, ?_⟩
  intro i
  exact hreal i

end IndexedPredictorFamily

end Mettapedia.Computability.PNP
