import Mettapedia.Computability.PNP.FiniteUniformRate

/-!
# P vs NP background theory: finite uniform success bounds

This file packages the rational rate layer into a cleaner "uniform success"
interface.  The main quantity is the one-step miss ratio

`((|X| - 1) / |X|)`,

which is strictly less than `1` on any nonempty finite input domain.  In these
terms the deceptive-sample rate decays like

`|Code(H)| * missRatio^m`,

and exact ERM recovery has the complementary lower bound.

This is still a fully finite and uniform-sampling result, not yet the full
i.i.d. or PAC-style generalization theorem.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- The uniform one-step miss ratio on a finite input domain. -/
noncomputable def uniformMissRatio (Input : Type u) [Fintype Input] : ℚ :=
  (((Fintype.card Input : ℚ) - 1) / Fintype.card Input)

theorem uniformMissRatio_lt_one (Input : Type u) [Fintype Input] [Nonempty Input] :
    uniformMissRatio Input < 1 := by
  unfold uniformMissRatio
  have hpos : (0 : ℚ) < Fintype.card Input := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Input)
  have hlt : (Fintype.card Input : ℚ) - 1 < Fintype.card Input := by
    exact sub_lt_self _ zero_lt_one
  exact (div_lt_one hpos).2 hlt

theorem uniformMissRatio_nonneg (Input : Type u) [Fintype Input] [Nonempty Input] :
    0 ≤ uniformMissRatio Input := by
  unfold uniformMissRatio
  have hpos : (0 : ℚ) < Fintype.card Input := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Input)
  have hcard : (1 : ℚ) ≤ Fintype.card Input := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card Input))
  exact div_nonneg (sub_nonneg.mpr hcard) hpos.le

theorem uniformMissRatio_le_one (Input : Type u) [Fintype Input] [Nonempty Input] :
    uniformMissRatio Input ≤ 1 :=
  (uniformMissRatio_lt_one Input).le

theorem uniformMissRatio_pow_le_one (Input : Type u) [Fintype Input] [Nonempty Input]
    (m : ℕ) :
    uniformMissRatio Input ^ m ≤ 1 :=
  pow_le_one₀ (uniformMissRatio_nonneg Input) (uniformMissRatio_le_one Input)

/-- The uniform miss-ratio failure term decreases as the sample length grows. -/
theorem uniformMissRatio_pow_le_pow_of_le (Input : Type u)
    [Fintype Input] [Nonempty Input] {m n : ℕ} (hmn : m ≤ n) :
    uniformMissRatio Input ^ n ≤ uniformMissRatio Input ^ m := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, hk⟩
  subst n
  rw [pow_add]
  exact
    mul_le_of_le_one_right
      (pow_nonneg (uniformMissRatio_nonneg Input) m)
      (uniformMissRatio_pow_le_one Input k)

namespace EncodedFamily

section UniformSuccess

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [Nonempty Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

theorem deceptiveRate_le_codeMul_uniformMissRatio_pow
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
  calc
    H.deceptiveRate target m
      ≤ (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
          ((Fintype.card Input : ℚ) ^ m)) :=
        H.deceptiveRate_le_bound target m
    _ = (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
      unfold uniformMissRatio
      rw [mul_div_assoc, ← div_pow]

omit [DecidableEq Output] in
theorem codeMul_uniformMissRatio_pow_le_of_le
    {m n : ℕ} (hmn : m ≤ n) :
    (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ n ≤
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
  exact
    mul_le_mul_of_nonneg_left
      (uniformMissRatio_pow_le_pow_of_le Input hmn)
      (by positivity)

theorem nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow
    (target : Input → Output) (m : ℕ) :
    1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
      H.nondeceptiveRate target m := by
  have hdeceptive :
      H.deceptiveRate target m ≤
        (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m :=
    H.deceptiveRate_le_codeMul_uniformMissRatio_pow target m
  have hstep :
      1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
        1 - H.deceptiveRate target m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hdeceptive) 1
  simpa [H.nondeceptiveRate_eq_one_sub_deceptiveRate target m] using hstep

theorem nondeceptiveRate_ge_one_sub_of_codeMul_uniformMissRatio_pow_le
    (target : Input → Output) (m : ℕ) {ε : ℚ}
    (hε :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ H.nondeceptiveRate target m := by
  have hstep :
      1 - ε ≤ 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hε) 1
  exact le_trans hstep <|
    H.nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow target m

theorem nondeceptiveRate_pos_of_codeMul_uniformMissRatio_pow_lt_one
    (target : Input → Output) (m : ℕ)
    (hlt :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < H.nondeceptiveRate target m := by
  have hpos :
      0 < 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    exact sub_pos.mpr hlt
  exact lt_of_lt_of_le hpos <|
    H.nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow target m

theorem nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow_of_le
    (target : Input → Output) {m n : ℕ} (hmn : m ≤ n) :
    1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
      H.nondeceptiveRate target n := by
  have hmon := H.codeMul_uniformMissRatio_pow_le_of_le hmn
  have hstep :
      1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
        1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ n := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hmon) 1
  exact le_trans hstep <|
    H.nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow target n

theorem exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
      H.exactRecoveryRate target m := by
  have hdeceptive :
      H.deceptiveRate target m ≤
        (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m :=
    H.deceptiveRate_le_codeMul_uniformMissRatio_pow target m
  have hone :
      1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
        1 - H.deceptiveRate target m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hdeceptive) 1
  exact le_trans hone (H.exactRecoveryRate_ge_one_sub_deceptiveRate target m htarget)

theorem exactRecoveryRate_ge_one_sub_of_codeMul_uniformMissRatio_pow_le
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    {ε : ℚ}
    (hε :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ H.exactRecoveryRate target m := by
  have hstep :
      1 - ε ≤ 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hε) 1
  exact le_trans hstep <|
    H.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow target m htarget

theorem exactRecoveryRate_pos_of_codeMul_uniformMissRatio_pow_lt_one
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hlt :
      (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < H.exactRecoveryRate target m := by
  have hpos :
      0 < 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m := by
    have : 1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m > 0 := by
      exact sub_pos.mpr hlt
    simpa using this
  exact lt_of_lt_of_le hpos <|
    H.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow target m htarget

theorem exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow_of_le
    [Nonempty H.Code]
    (target : Input → Output) {m n : ℕ}
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hmn : m ≤ n) :
    1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
      H.exactRecoveryRate target n := by
  have hmon := H.codeMul_uniformMissRatio_pow_le_of_le hmn
  have hstep :
      1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ m ≤
        1 - (Fintype.card H.Code : ℚ) * uniformMissRatio Input ^ n := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (neg_le_neg hmon) 1
  exact le_trans hstep <|
    H.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow target n htarget

end UniformSuccess

end EncodedFamily

namespace BitEncodedClassifierFamily

section UniformSuccess

variable {Input : Type u} [Fintype Input] [Nonempty Input]
variable {s : ℕ} (F : BitEncodedClassifierFamily Input s)

instance toEncodedFamilyCodeNonempty :
    Nonempty F.toEncodedFamily.Code := by
  change Nonempty (BitCode s)
  exact ⟨fun _ => false⟩

/-- Bit-budget form of the deceptive-rate bound: an `s`-bit classifier family
has deceptive uniform sample rate at most `2^s * ρ_X^m`. -/
theorem deceptiveRate_le_bitBudget_uniformMissRatio_pow
    (target : Input → Bool) (m : ℕ) :
    F.toEncodedFamily.deceptiveRate target m ≤
      (2 ^ s : ℚ) * uniformMissRatio Input ^ m := by
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    F.toEncodedFamily.deceptiveRate_le_codeMul_uniformMissRatio_pow target m

theorem bitBudget_uniformMissRatio_pow_le_of_le
    {m n : ℕ} (hmn : m ≤ n) :
    (2 ^ s : ℚ) * uniformMissRatio Input ^ n ≤
      (2 ^ s : ℚ) * uniformMissRatio Input ^ m := by
  exact
    mul_le_mul_of_nonneg_left
      (uniformMissRatio_pow_le_pow_of_le Input hmn)
      (by positivity)

/-- Bit-budget form of the non-deceptive-rate lower bound. -/
theorem nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow
    (target : Input → Bool) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target m := by
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    F.toEncodedFamily.nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow
      target m

/-- Epsilon-style bit-budget non-deceptive-rate corollary. -/
theorem nondeceptiveRate_ge_one_sub_of_bitBudget_uniformMissRatio_pow_le
    (target : Input → Bool) (m : ℕ) {ε : ℚ}
    (hε : (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.nondeceptiveRate target m := by
  have hε' :
      (Fintype.card F.toEncodedFamily.Code : ℚ) *
          uniformMissRatio Input ^ m ≤ ε := by
    simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using hε
  exact
    F.toEncodedFamily.nondeceptiveRate_ge_one_sub_of_codeMul_uniformMissRatio_pow_le
      target m hε'

/-- Positivity form of the bit-budget non-deceptive-rate bound. -/
theorem nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
    (target : Input → Bool) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.toEncodedFamily.nondeceptiveRate target m := by
  have hlt' :
      (Fintype.card F.toEncodedFamily.Code : ℚ) *
          uniformMissRatio Input ^ m < 1 := by
    simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using hlt
  exact
    F.toEncodedFamily.nondeceptiveRate_pos_of_codeMul_uniformMissRatio_pow_lt_one
      target m hlt'

theorem nondeceptiveRate_ge_one_sub_bitBudget_uniformMissRatio_pow_of_le
    (target : Input → Bool) {m n : ℕ} (hmn : m ≤ n) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.nondeceptiveRate target n := by
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    F.toEncodedFamily.nondeceptiveRate_ge_one_sub_codeMul_uniformMissRatio_pow_of_le
      target hmn

/-- Bit-budget form of the exact ERM recovery lower bound.  This is the
finite-uniform positive bridge needed by any grassroots compression route:
once the target is realized by an `s`-bit family, exact ERM recovery has success
rate at least `1 - 2^s * ρ_X^m`. -/
theorem exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target m := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    F.toEncodedFamily.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow
      target m htarget

/-- Epsilon-style bit-budget recovery corollary. -/
theorem exactRecoveryRate_ge_one_sub_of_bitBudget_uniformMissRatio_pow_le
    (target : Input → Bool) (m : ℕ) {ε : ℚ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hε : (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤ ε) :
    1 - ε ≤ F.toEncodedFamily.exactRecoveryRate target m := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  have hε' :
      (Fintype.card F.toEncodedFamily.Code : ℚ) *
          uniformMissRatio Input ^ m ≤ ε := by
    simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using hε
  exact
    F.toEncodedFamily.exactRecoveryRate_ge_one_sub_of_codeMul_uniformMissRatio_pow_le
      target m htarget hε'

/-- Positivity form of the bit-budget recovery bound. -/
theorem exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  have hlt' :
      (Fintype.card F.toEncodedFamily.Code : ℚ) *
          uniformMissRatio Input ^ m < 1 := by
    simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using hlt
  exact
    F.toEncodedFamily.exactRecoveryRate_pos_of_codeMul_uniformMissRatio_pow_lt_one
      target m htarget hlt'

theorem exactRecoveryRate_ge_one_sub_bitBudget_uniformMissRatio_pow_of_le
    (target : Input → Bool) {m n : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hmn : m ≤ n) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      F.toEncodedFamily.exactRecoveryRate target n := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  simpa [BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    F.toEncodedFamily.exactRecoveryRate_ge_one_sub_codeMul_uniformMissRatio_pow_of_le
      target htarget hmn

/-- Cardinality-threshold form of bit-budget rate positivity.  This version is
often easier to use before rewriting the threshold as a rational miss-ratio
bound. -/
theorem exactRecoveryRate_pos_of_bitBudget_bound_lt
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    0 < F.toEncodedFamily.exactRecoveryRate target m := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  have htarget' :
      ∃ c : F.toEncodedFamily.Code, F.toEncodedFamily.decode c = target := by
    change ∃ c : BitCode s, F.decode c = target
    exact htarget
  have hbound' :
      Fintype.card F.toEncodedFamily.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m := by
    change Fintype.card (BitCode s) * (Fintype.card Input - 1) ^ m <
      Fintype.card Input ^ m
    rw [card_bitCode]
    exact hbound
  exact
    F.toEncodedFamily.exactRecoveryRate_pos_of_bound_lt
      target m htarget' hbound'

end UniformSuccess

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
