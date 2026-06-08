import Mettapedia.Computability.PNP.BitFamilyUniformSuccessBinary

/-!
# Regression checks for binary bit-family success rates

These wrappers pin the strict positivity bridge from `s < m` to the uniform
exact-recovery rate on two-point input domains.
-/

namespace Mettapedia.Computability.PNP.BitFamilyUniformSuccessBinaryRegression

open Mettapedia.Computability.PNP

universe u

theorem card_two_exact_recovery_rate_positive_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (hcard : Fintype.card Input = 2)
    (target : Input → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_of_card_eq_two_of_lt_sampleSize
      hcard target htarget hsm

theorem bool_exact_recovery_rate_positive_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_pos_bool_of_lt_sampleSize target htarget hsm

theorem bool_deceptive_rate_quantitative_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ) :
    F.toEncodedFamily.deceptiveRate target m ≤
      (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m := by
  exact F.deceptiveRate_le_bool_bitBudget_pow target m

theorem bool_nondeceptive_rate_quantitative_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_ge_one_sub_bool_bitBudget_pow target m

theorem bool_nondeceptive_rate_epsilon_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ) {ε : ℚ}
    (hε : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_ge_one_sub_of_bool_bitBudget_pow_le target m hε

theorem bool_nondeceptive_rate_positive_quantitative_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_pos_bool_of_bitBudget_pow_lt_one target m hlt

theorem bool_exact_recovery_rate_quantitative_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target) :
    1 - (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_ge_one_sub_bool_bitBudget_pow target m htarget

theorem bool_exact_recovery_rate_epsilon_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hε : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_of_bool_bitBudget_pow_le
      target m htarget hε

theorem bool_exact_recovery_rate_positive_quantitative_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hlt : (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_bool_of_bitBudget_pow_lt_one
      target m htarget hlt

theorem bool_bit_budget_margin_bound_regression
    {s m k : ℕ} (hskm : s + k ≤ m) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ (1 / 2 : ℚ) ^ k := by
  exact BitEncodedClassifierFamily.bool_bitBudget_pow_le_margin_pow hskm

theorem bool_margin_pow_strict_regression
    {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℚ) ^ k < 1 := by
  exact BitEncodedClassifierFamily.bool_margin_pow_lt_one hk

theorem bool_bit_budget_margin_strict_regression
    {s m k : ℕ} (hskm : s + k ≤ m) (hk : 0 < k) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1 := by
  exact
    BitEncodedClassifierFamily.bool_bitBudget_pow_lt_one_of_positive_margin
      hskm hk

theorem bool_exact_recovery_rate_margin_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_bool_margin_pow
      target m k htarget hskm

theorem bool_nondeceptive_rate_margin_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) :
    1 - (1 / 2 : ℚ) ^ k ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_ge_one_sub_bool_margin_pow
      target m k hskm

theorem bool_bit_budget_margin_epsilon_regression
    {s m k : ℕ} {ε : ℚ}
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m ≤ ε := by
  exact
    BitEncodedClassifierFamily.bool_bitBudget_pow_le_of_margin_pow_le
      hskm hε

theorem bool_exact_recovery_rate_margin_epsilon_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_of_bool_margin_pow_le
      target m k htarget hskm hε

theorem bool_nondeceptive_rate_margin_epsilon_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ) {ε : ℚ}
    (hskm : s + k ≤ m) (hε : (1 / 2 : ℚ) ^ k ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_ge_one_sub_of_bool_margin_pow_le
      target m k hskm hε

theorem bool_exact_recovery_rate_positive_margin_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_bool_of_positive_margin
      target m k htarget hskm hk

theorem bool_nondeceptive_rate_positive_margin_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) (m k : ℕ)
    (hskm : s + k ≤ m) (hk : 0 < k) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_pos_bool_of_positive_margin
      target m k hskm hk

theorem bool_bit_budget_strict_of_lt_sample_size_regression
    {s m : ℕ} (hsm : s < m) :
    (2 ^ s : ℚ) * (1 / 2 : ℚ) ^ m < 1 := by
  exact
    BitEncodedClassifierFamily.bool_bitBudget_pow_lt_one_of_lt_sampleSize hsm

theorem bool_nondeceptive_rate_positive_of_lt_sample_size_regression
    {s : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool) {m : ℕ}
    (hsm : s < m) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_pos_bool_of_lt_sampleSize target hsm

end Mettapedia.Computability.PNP.BitFamilyUniformSuccessBinaryRegression
