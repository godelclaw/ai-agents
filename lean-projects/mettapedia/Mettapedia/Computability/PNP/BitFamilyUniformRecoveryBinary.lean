import Mettapedia.Computability.PNP.BitFamilyUniformRecovery

/-!
# P vs NP grassroots: binary-input bit-family recovery

This file specializes the finite bit-budget recovery threshold to two-point
input domains.  On such domains the abstract cardinality obligation

`2^s * (|X| - 1)^m < |X|^m`

collapses to the simple sample-size obligation `s < m`.
-/

namespace Mettapedia.Computability.PNP

universe u

namespace BitEncodedClassifierFamily

section CardinalityTwo

variable {Input : Type u} [Fintype Input]
variable {s : ℕ}

/-- On a two-point input domain, the bit-budget counting threshold follows
from the simple sample-size inequality `s < m`. -/
theorem bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize
    (hcard : Fintype.card Input = 2) {m : ℕ} (hsm : s < m) :
    2 ^ s * (Fintype.card Input - 1) ^ m <
      Fintype.card Input ^ m := by
  have hpow : 2 ^ s < 2 ^ m :=
    Nat.pow_lt_pow_right Nat.one_lt_two hsm
  simpa [hcard] using hpow

variable (F : BitEncodedClassifierFamily Input s)

/-- Cardinality-two form of the non-deceptive-sample existence theorem. -/
theorem exists_nondeceptiveSample_of_card_eq_two_of_lt_sampleSize
    (hcard : Fintype.card Input = 2)
    (target : Input → Bool) {m : ℕ} (hsm : s < m) :
    ∃ sample : PointSample Input m,
      ¬ F.toEncodedFamily.IsDeceptiveSample target sample := by
  exact
    F.exists_nondeceptiveSample_of_bitBudget_bound_lt target m
      (bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize hcard hsm)

/-- Cardinality-two form of the exact bit-family ERM recovery theorem. -/
theorem exists_sample_empiricalRiskPredictor_eq_target_of_card_eq_two_of_lt_sampleSize
    (hcard : Fintype.card Input = 2)
    (target : Input → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact
    F.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
      target m htarget
      (bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize hcard hsm)

end CardinalityTwo

section Bool

variable {s : ℕ} (F : BitEncodedClassifierFamily Bool s)

/-- Boolean-domain threshold arithmetic: `s < m` implies the finite recovery
cardinality gap. -/
theorem bool_bitBudget_bound_lt_of_lt_sampleSize
    {m : ℕ} (hsm : s < m) :
    2 ^ s * (Fintype.card Bool - 1) ^ m <
      Fintype.card Bool ^ m := by
  exact bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize (Input := Bool) (by simp) hsm

/-- Boolean-domain non-deceptive sample existence from `s < m`. -/
theorem exists_bool_nondeceptiveSample_of_lt_sampleSize
    (target : Bool → Bool) {m : ℕ} (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      ¬ F.toEncodedFamily.IsDeceptiveSample target sample := by
  exact
    F.exists_nondeceptiveSample_of_card_eq_two_of_lt_sampleSize
      (by simp) target hsm

/-- Boolean-domain exact bit-family ERM recovery from `s < m`. -/
theorem exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize
    (target : Bool → Bool) {m : ℕ}
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact
    F.exists_sample_empiricalRiskPredictor_eq_target_of_card_eq_two_of_lt_sampleSize
      (by simp) target htarget hsm

end Bool

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
