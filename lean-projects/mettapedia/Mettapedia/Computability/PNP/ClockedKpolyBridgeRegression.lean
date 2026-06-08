import Mettapedia.Computability.PNP.ClockedKpolyBridge

/-!
# Regression checks for the clocked `Kpoly` bridge kernel

These wrappers pin the finite counting layer only: once a target is realized by
a clocked `s`-bit family, the existing finite-uniform recovery bounds apply.
They do not assert that any manuscript decoder has been realized by such a
family.
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyBridgeRegression

open Mettapedia.Computability.PNP

universe u v

theorem clocked_of_bit_family_underlying_regression
    {Input : Type u} {s clock : ℕ}
    (F : BitEncodedClassifierFamily Input s) :
    (ClockedBitCodeFamily.ofBitEncodedClassifierFamily
        (Input := Input) (s := s) clock F).toBitEncodedClassifierFamily = F := by
  exact ClockedBitCodeFamily.toBitEncodedClassifierFamily_ofBitEncodedClassifierFamily
    (Input := Input) (s := s) clock F

theorem clocked_of_bit_family_realizes_iff_regression
    {Input : Type u} {s clock : ℕ}
    (F : BitEncodedClassifierFamily Input s) (target : Input → Bool) :
    (ClockedBitCodeFamily.ofBitEncodedClassifierFamily
        (Input := Input) (s := s) clock F).Realizes target ↔
      ∃ code : BitCode s, F.decode code = target := by
  exact ClockedBitCodeFamily.ofBitEncodedClassifierFamily_realizes_iff
    (Input := Input) (s := s) clock F target

theorem clocked_of_bit_family_exactRecoveryRate_regression
    {Input : Type u} [Fintype Input] {s clock : ℕ}
    (F : BitEncodedClassifierFamily Input s) (target : Input → Bool) (m : ℕ) :
    (ClockedBitCodeFamily.ofBitEncodedClassifierFamily
        (Input := Input) (s := s) clock F).exactRecoveryRate target m =
      F.toEncodedFamily.exactRecoveryRate target m := by
  exact ClockedBitCodeFamily.exactRecoveryRate_ofBitEncodedClassifierFamily
    (Input := Input) (s := s) clock F target m

theorem clocked_of_bit_family_nondeceptiveRate_regression
    {Input : Type u} [Fintype Input] {s clock : ℕ}
    (F : BitEncodedClassifierFamily Input s) (target : Input → Bool) (m : ℕ) :
    (ClockedBitCodeFamily.ofBitEncodedClassifierFamily
        (Input := Input) (s := s) clock F).nondeceptiveRate target m =
      F.toEncodedFamily.nondeceptiveRate target m := by
  exact ClockedBitCodeFamily.nondeceptiveRate_ofBitEncodedClassifierFamily
    (Input := Input) (s := s) clock F target m

theorem clocked_of_bit_family_empiricalRiskPredictor_regression
    {Input : Type u} {s clock : ℕ}
    (F : BitEncodedClassifierFamily Input s) (sample : Sample Input Bool) :
    (ClockedBitCodeFamily.ofBitEncodedClassifierFamily
        (Input := Input) (s := s) clock F).empiricalRiskPredictor sample =
      F.empiricalRiskPredictor sample := by
  exact ClockedBitCodeFamily.empiricalRiskPredictor_ofBitEncodedClassifierFamily
    (Input := Input) (s := s) clock F sample

theorem clocked_card_realized_le_bitBudget_regression
    {Input : Type u} {s clock : ℕ}
    (F : ClockedBitCodeFamily Input s clock) :
    Fintype.card
        (EncodedFamily.realized F.toBitEncodedClassifierFamily.toEncodedFamily) ≤ 2 ^ s := by
  exact F.card_realized_le_bitBudget

theorem indexed_hasBitBudget_of_realizedByClockedBitFamily_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    {F : ClockedBitCodeFamily Input s clock}
    (hreal : G.RealizedByClockedBitFamily F) :
    G.HasBitBudget s := by
  exact IndexedPredictorFamily.hasBitBudget_of_realizedByClockedBitFamily hreal

theorem clocked_nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_ge_one_sub_uniformMissRatio_pow target m

theorem clocked_exists_nondeceptiveSample_of_bitBudget_bound_lt_regression
    {Input : Type u} [Fintype Input]
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ¬ F.toBitEncodedClassifierFamily.toEncodedFamily.IsDeceptiveSample target sample := by
  exact F.exists_nondeceptiveSample_of_bitBudget_bound_lt target m hbound

theorem clocked_exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_regression
    {Input : Type u} [Fintype Input]
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (htarget : F.Realizes target)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact F.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
    target m htarget hbound

theorem clocked_exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Input s clock)
    (target : Input → Bool) (m : ℕ)
    (htarget : F.Realizes target) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_ge_one_sub_uniformMissRatio_pow target m htarget

theorem clocked_nondeceptiveRate_ge_one_sub_bool_margin_pow_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_ge_one_sub_bool_margin_pow target m k hskm

theorem clocked_exactRecoveryRate_ge_one_sub_bool_margin_pow_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : F.Realizes target)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_ge_one_sub_bool_margin_pow target m k htarget hskm

theorem clocked_nondeceptiveRate_pos_bool_of_positive_margin_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_pos_bool_of_positive_margin
      target m k hskm hk

theorem clocked_exists_bool_nondeceptiveSample_of_lt_sampleSize_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      ¬ F.toBitEncodedClassifierFamily.toEncodedFamily.IsDeceptiveSample target sample := by
  exact F.exists_bool_nondeceptiveSample_of_lt_sampleSize target hsm

theorem clocked_exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (htarget : F.Realizes target)
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact F.exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize
    target htarget hsm

theorem clocked_exactRecoveryRate_pos_bool_of_positive_margin_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : F.Realizes target)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_bool_of_positive_margin
      target m k htarget hskm hk

theorem clocked_exactRecoveryRate_pos_bool_of_lt_sampleSize_regression
    {s clock : ℕ}
    (F : ClockedBitCodeFamily Bool s clock)
    (target : Bool → Bool) {m : ℕ}
    (htarget : F.Realizes target)
    (hsm : s < m) :
    0 < F.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_pos_bool_of_lt_sampleSize target htarget hsm

end Mettapedia.Computability.PNP.ClockedKpolyBridgeRegression
