import Mettapedia.Computability.PNP.BitFamilyUniformRecoveryBinary
import Mathlib.Tactic

/-!
# P vs NP background theory: lower bounds forced by finite recovery gaps

`BitFamilyUniformRecoveryBinary.lean` showed that on a two-point input domain,
the counting threshold

`2^s * (|X| - 1)^m < |X|^m`

follows from the simple sample-size inequality `s < m`.

This file records the converse inequality on every finite input domain with at
least two points: the same counting threshold can only hold when the bit budget
is strictly smaller than the sample length.
-/

namespace Mettapedia.Computability.PNP

universe u

namespace BitEncodedClassifierFamily

section SampleLowerBound

variable {Input : Type u} [Fintype Input]
variable {s m : ℕ}

/-- Any finite input domain with at least two points satisfies
`|X| ≤ 2 * (|X| - 1)`. -/
theorem card_le_two_mul_pred_of_two_le_card
    (hcard : 2 ≤ Fintype.card Input) :
    Fintype.card Input ≤ 2 * (Fintype.card Input - 1) := by
  omega

/-- On any finite input domain with at least two points, if the sample length
does not exceed the bit budget, then the finite recovery counting term is at
least the full sample-space cardinality. -/
theorem bitBudget_bound_ge_of_sampleSize_le_of_two_le_card
    (hcard : 2 ≤ Fintype.card Input)
    (hms : m ≤ s) :
    Fintype.card Input ^ m ≤
      2 ^ s * (Fintype.card Input - 1) ^ m := by
  calc
    Fintype.card Input ^ m ≤ (2 * (Fintype.card Input - 1)) ^ m := by
      exact
        Nat.pow_le_pow_left
          (card_le_two_mul_pred_of_two_le_card (Input := Input) hcard)
          m
    _ = 2 ^ m * (Fintype.card Input - 1) ^ m := by
      rw [Nat.mul_pow]
    _ ≤ 2 ^ s * (Fintype.card Input - 1) ^ m := by
      exact
        Nat.mul_le_mul_right
          ((Fintype.card Input - 1) ^ m)
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hms)

/-- Therefore the finite recovery counting threshold on any input domain with
at least two points forces the strict sample-size inequality `s < m`. -/
theorem lt_sampleSize_of_two_le_card_of_bitBudget_bound_lt
    (hcard : 2 ≤ Fintype.card Input)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    s < m := by
  by_contra hsm
  exact
    (not_lt_of_ge
      (bitBudget_bound_ge_of_sampleSize_le_of_two_le_card
        (Input := Input) (s := s) (m := m)
        hcard (Nat.not_lt.mp hsm))) hbound

/-- On a two-point input domain, the finite recovery counting threshold is
equivalent to the simple sample-size inequality `s < m`. -/
theorem bitBudget_bound_lt_iff_lt_sampleSize_of_card_eq_two
    (hcard : Fintype.card Input = 2) :
    (2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) ↔
      s < m := by
  constructor
  · intro hbound
    exact
      lt_sampleSize_of_two_le_card_of_bitBudget_bound_lt
        (Input := Input) (s := s) (m := m)
        (by omega) hbound
  · intro hsm
    exact
      bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize
        (Input := Input) (s := s) hcard hsm

end SampleLowerBound

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
