import Mettapedia.Computability.PNP.FiniteUniformSuccess

/-!
# Regression checks for finite uniform bit-budget success bounds

These wrappers pin the bit-budget specialization of the finite uniform ERM
success theorem.  They keep the grassroots PNP compression route connected to
the explicit `2^s` code budget.
-/

namespace Mettapedia.Computability.PNP.FiniteUniformSuccessRegression

open Mettapedia.Computability.PNP

universe u

theorem uniform_miss_ratio_nonnegative_regression
    (Input : Type u) [Fintype Input] [Nonempty Input] :
    0 ≤ uniformMissRatio Input := by
  exact uniformMissRatio_nonneg Input

theorem uniform_miss_ratio_at_most_one_regression
    (Input : Type u) [Fintype Input] [Nonempty Input] :
    uniformMissRatio Input ≤ 1 := by
  exact uniformMissRatio_le_one Input

theorem uniform_miss_ratio_power_antitone_regression
    (Input : Type u) [Fintype Input] [Nonempty Input] {m n : ℕ}
    (hmn : m ≤ n) :
    uniformMissRatio Input ^ n ≤ uniformMissRatio Input ^ m := by
  exact uniformMissRatio_pow_le_pow_of_le Input hmn

theorem bit_family_deceptive_rate_bound_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) :
    F.toEncodedFamily.deceptiveRate target m ≤
      (2 ^ s : ℚ) * uniformMissRatio Input ^ m := by
  exact F.deceptiveRate_le_bitBudget_uniformMissRatio_pow target m

theorem bit_family_failure_term_antitone_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s m n : ℕ} (hmn : m ≤ n) :
    (2 ^ s : ℚ) * uniformMissRatio Input ^ n ≤
      (2 ^ s : ℚ) * uniformMissRatio Input ^ m := by
  exact
    BitEncodedClassifierFamily.bitBudget_uniformMissRatio_pow_le_of_le
      (Input := Input) (s := s) hmn

theorem bit_family_nondeceptive_rate_bound_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target m := by
  exact F.nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow target m

theorem bit_family_nondeceptive_rate_epsilon_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) {ε : ℚ}
    (hε : (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_ge_one_sub_of_bitBudget_uniformMissRatio_pow_le
      target m hε

theorem bit_family_nondeceptive_rate_positive_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  exact
    F.nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      target m hlt

theorem bit_family_nondeceptive_rate_bound_of_sample_le_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s m n : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (hmn : m ≤ n) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target n := by
  exact F.nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow_of_le target hmn

theorem bit_family_exact_recovery_rate_bound_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target m := by
  exact F.exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow target m htarget

theorem bit_family_exact_recovery_rate_epsilon_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hε : (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_ge_one_sub_of_bitBudget_uniformMissRatio_pow_le
      target m htarget hε

theorem bit_family_exact_recovery_rate_positive_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  exact
    F.exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      target m htarget hlt

theorem bit_family_exact_recovery_rate_bound_of_sample_le_regression
    {Input : Type u} [Fintype Input] [Nonempty Input]
    {s m n : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hmn : m ≤ n) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target n := by
  exact
    F.exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow_of_le
      target htarget hmn

end Mettapedia.Computability.PNP.FiniteUniformSuccessRegression
