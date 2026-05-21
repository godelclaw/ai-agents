import Mettapedia.Computability.PNP.BitFamilyUniformRecoveryBinary
import Mettapedia.Computability.PNP.FiniteUniformSuccess

/-!
# P vs NP grassroots: binary-input bit-family success rates

This file connects the binary-input recovery threshold `s < m` to the rational
uniform exact-recovery rate.  The corresponding existential recovery theorem
lives in `BitFamilyUniformRecoveryBinary.lean`; here the conclusion is that the
uniform density of exact ERM recovery samples is strictly positive.
-/

namespace Mettapedia.Computability.PNP

universe u

namespace BitEncodedClassifierFamily

section CardinalityTwo

variable {Input : Type u} [Fintype Input]
variable {s : ℕ} (F : BitEncodedClassifierFamily Input s)

/-- On any two-point input domain, `s < m` gives a strictly positive uniform
exact-recovery rate for every realized target. -/
theorem exactRecoveryRate_pos_of_card_eq_two_of_lt_sampleSize
    (hcard : Fintype.card Input = 2)
    (target : Input → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  letI : Nonempty Input := by
    exact Fintype.card_pos_iff.mp (by simp [hcard])
  exact
    F.exactRecoveryRate_pos_of_bitBudget_bound_lt target m htarget
      (bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize hcard hsm)

end CardinalityTwo

section Bool

variable {s : ℕ} (F : BitEncodedClassifierFamily Bool s)

/-- The uniform miss ratio on the Boolean input domain is exactly `1 / 2`. -/
theorem uniformMissRatio_bool :
    uniformMissRatio Bool = (1 / 2 : ℚ) := by
  norm_num [uniformMissRatio]

/-- Boolean-domain deceptive-rate bound with the miss ratio simplified to
`1 / 2`. -/
theorem deceptiveRate_le_bool_bitBudget_pow
    (target : Bool → Bool) (m : ℕ) :
    F.toEncodedFamily.deceptiveRate target m ≤
      (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m := by
  simpa [uniformMissRatio_bool] using
    F.deceptiveRate_le_bitBudget_uniformMissRatio_pow target m

/-- Boolean-domain non-deceptive-rate lower bound with the miss ratio
simplified to `1 / 2`. -/
theorem nondeceptiveRate_ge_one_sub_bool_bitBudget_pow
    (target : Bool → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target m := by
  simpa [uniformMissRatio_bool] using
    F.nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow target m

/-- Boolean-domain epsilon corollary for non-deceptive samples. -/
theorem nondeceptiveRate_ge_one_sub_of_bool_bitBudget_pow_le
    (target : Bool → Bool) (m : ℕ) {ε : ℚ}
    (hε : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    le_trans
      (by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_left (neg_le_neg hε) 1)
      (F.nondeceptiveRate_ge_one_sub_bool_bitBudget_pow target m)

/-- Boolean-domain positivity for non-deceptive samples from the explicit
quantitative failure bound. -/
theorem nondeceptiveRate_pos_bool_of_bitBudget_pow_lt_one
    (target : Bool → Bool) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  have hpos :
      0 < 1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m := by
    exact sub_pos.mpr hlt
  exact lt_of_lt_of_le hpos
    (F.nondeceptiveRate_ge_one_sub_bool_bitBudget_pow target m)

/-- Boolean-domain exact recovery lower bound with the miss ratio simplified to
`1 / 2`. -/
theorem exactRecoveryRate_ge_one_sub_bool_bitBudget_pow
    (target : Bool → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target m := by
  simpa [uniformMissRatio_bool] using
    F.exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow target m htarget

/-- Boolean-domain epsilon corollary for exact recovery. -/
theorem exactRecoveryRate_ge_one_sub_of_bool_bitBudget_pow_le
    (target : Bool → Bool) (m : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hε : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    le_trans
      (by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_left (neg_le_neg hε) 1)
      (F.exactRecoveryRate_ge_one_sub_bool_bitBudget_pow target m htarget)

/-- Boolean-domain positivity from the explicit quantitative failure bound. -/
theorem exactRecoveryRate_pos_bool_of_bitBudget_pow_lt_one
    (target : Bool → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hlt : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  have hpos :
      0 < 1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m := by
    exact sub_pos.mpr hlt
  exact lt_of_lt_of_le hpos
    (F.exactRecoveryRate_ge_one_sub_bool_bitBudget_pow target m htarget)

/-- If the Boolean sample length exceeds the bit budget by at least `k`, then
the explicit finite-uniform failure term is at most `(1 / 2)^k`. -/
theorem bool_bitBudget_pow_le_margin_pow
    {s m k : ℕ} (hskm : s + k ≤ m) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ (1 / 2 : ℚ) ^ k := by
  rcases Nat.exists_eq_add_of_le hskm with ⟨r, hr⟩
  subst m
  have hcancel : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ s = 1 := by
    rw [show (1 / 2 : ℚ) = (2 : ℚ)⁻¹ by norm_num, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero s (by norm_num : (2 : ℚ) ≠ 0))
  calc
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ (s + k + r)
        = ((2 ^ s : ℚ) * (1 / 2 : ℚ) ^ s) *
            ((1 / 2 : ℚ) ^ k * (1 / 2 : ℚ) ^ r) := by
          rw [pow_add, pow_add]
          ring
    _ = (1 / 2 : ℚ) ^ k * (1 / 2 : ℚ) ^ r := by
          rw [hcancel, one_mul]
    _ ≤ (1 / 2 : ℚ) ^ k := by
          exact
            mul_le_of_le_one_right (by positivity)
              (pow_le_one₀ (by norm_num) (by norm_num : (1 / 2 : ℚ) ≤ 1))

/-- A positive Boolean sample margin has strictly subunit residual failure. -/
theorem bool_margin_pow_lt_one {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℚ) ^ k < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num : (1 / 2 : ℚ) < 1) (Nat.ne_of_gt hk)

/-- Strict form of the Boolean sample-margin failure bound. -/
theorem bool_bitBudget_pow_lt_one_of_positive_margin
    {s m k : ℕ} (hskm : s + k ≤ m) (hk : 0 < k) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1 :=
  lt_of_le_of_lt (bool_bitBudget_pow_le_margin_pow hskm) (bool_margin_pow_lt_one hk)

/-- Boolean-domain exact recovery lower bound in sample-margin form.  If the
sample length is at least the bit budget plus `k`, exact ERM recovery succeeds
on at least a `1 - (1 / 2)^k` fraction of uniform samples. -/
theorem exactRecoveryRate_ge_one_sub_bool_margin_pow
    (target : Bool → Bool) (m k : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_of_bool_bitBudget_pow_le
      target m htarget (bool_bitBudget_pow_le_margin_pow hskm)

/-- Boolean-domain non-deceptive-rate lower bound in sample-margin form.  If
the sample length is at least the bit budget plus `k`, then at least a
`1 - (1 / 2)^k` fraction of uniform samples are non-deceptive. -/
theorem nondeceptiveRate_ge_one_sub_bool_margin_pow
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_ge_one_sub_of_bool_bitBudget_pow_le
      target m (bool_bitBudget_pow_le_margin_pow hskm)

/-- Epsilon form of the Boolean sample-margin failure bound.  If the sample
length exceeds the bit budget by at least `k` and `(1 / 2)^k ≤ ε`, then the
explicit finite-uniform failure term is at most `ε`. -/
theorem bool_bitBudget_pow_le_of_margin_pow_le
    {s m k : ℕ} {ε : ℚ}
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε := by
  exact le_trans (bool_bitBudget_pow_le_margin_pow hskm) hε

/-- Epsilon form of the Boolean sample-margin exact-recovery bound. -/
theorem exactRecoveryRate_ge_one_sub_of_bool_margin_pow_le
    (target : Bool → Bool) (m k : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_of_bool_bitBudget_pow_le
      target m htarget (bool_bitBudget_pow_le_of_margin_pow_le hskm hε)

/-- Epsilon form of the Boolean sample-margin non-deceptive-rate bound. -/
theorem nondeceptiveRate_ge_one_sub_of_bool_margin_pow_le
    (target : Bool → Bool) (m k : ℕ) {ε : ℚ}
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_ge_one_sub_of_bool_bitBudget_pow_le
      target m (bool_bitBudget_pow_le_of_margin_pow_le hskm hε)

/-- Positive-margin Boolean-domain exact-recovery positivity. -/
theorem exactRecoveryRate_pos_bool_of_positive_margin
    (target : Bool → Bool) (m k : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_bool_of_bitBudget_pow_lt_one
      target m htarget (bool_bitBudget_pow_lt_one_of_positive_margin hskm hk)

/-- Positive-margin Boolean-domain non-deceptive-rate positivity. -/
theorem nondeceptiveRate_pos_bool_of_positive_margin
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_pos_bool_of_bitBudget_pow_lt_one
      target m (bool_bitBudget_pow_lt_one_of_positive_margin hskm hk)

/-- Boolean-domain strict failure bound from the concrete sample-size
inequality `s < m`. -/
theorem bool_bitBudget_pow_lt_one_of_lt_sampleSize
    {s m : ℕ} (hsm : s < m) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1 := by
  exact
    bool_bitBudget_pow_lt_one_of_positive_margin
      (Nat.succ_le_iff.mpr hsm) Nat.zero_lt_one

/-- Boolean-domain rate positivity from the concrete sample-size inequality
`s < m`. -/
theorem exactRecoveryRate_pos_bool_of_lt_sampleSize
    (target : Bool → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_of_card_eq_two_of_lt_sampleSize
      (by simp) target htarget hsm

/-- Boolean-domain non-deceptive-rate positivity from the concrete sample-size
inequality `s < m`. -/
theorem nondeceptiveRate_pos_bool_of_lt_sampleSize
    (target : Bool → Bool) {m : ℕ}
    (hsm : s < m) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_pos_bool_of_bitBudget_pow_lt_one
      target m (bool_bitBudget_pow_lt_one_of_lt_sampleSize hsm)

end Bool

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
