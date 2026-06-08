import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMWidthCharacterization
import Mettapedia.Computability.PNP.BitFamilyUniformRecoveryLowerBound
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mathlib.Tactic

/-!
# P vs NP route consequence: the current sparse-threshold ERM liveness packet
forces large samples

The surviving actual switched-local sparse-threshold ERM branch is now known to
be exactly the noncompressing injective-extractor branch on `BitVec n`, under
the standard point-block width and finite counting-gap hypotheses.

This file extracts the next honest consequence of that same counting-gap
hypothesis.  It is not a new obstruction theorem for the branch in full
generality.  It proves a conditional lower bound attached to the current
liveness packet:

* the point-block counting gap itself forces sample size larger than the
  point-block bit budget;
* on `BitVec n`, that means `m > 2^(2*(r + 2k) + 1)`;
* and any full-rule actual switched-local packet at width `r` therefore needs
  `m > 2^(2*(n + 2k) + 1)` once the earlier width characterization yields
  `n ≤ r`.
-/

namespace Mettapedia.Computability.PNP

section GapLowerBound

variable {Z : Type*} [Fintype Z] {r k m : ℕ}

/-- If the exact visible surface has at least two points, then the standard
point-block sparse-threshold counting gap already forces the sample size to
exceed the point-block bit budget. -/
theorem sparseThresholdPointBlockBudget_lt_sampleSize_of_two_le_surfaceCard
    (hcard : 2 ≤ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    2 * allAffinePointBlockFeatureCount (r + (k + k)) < m := by
  exact
    BitEncodedClassifierFamily.lt_sampleSize_of_two_le_card_of_bitBudget_bound_lt
      (Input := ExactVisiblePostSwitchSurface Z k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (m := m)
      hcard hbound

end GapLowerBound

section BitVec

variable {n r k m : ℕ}

/-- Any nontrivial exact visible `BitVec` surface has at least two points. -/
theorem two_le_card_exactVisiblePostSwitchSurface_bitVec_of_width_pos
    (hvis : 0 < n + (k + k)) :
    2 ≤ Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
  rw [card_exactVisiblePostSwitchSurface_bitVec]
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n + 2 * k) := by
      exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)

/-- The point-block sparse-threshold bit budget has the explicit closed form
`2^(2*d + 1)`. -/
theorem sparseThresholdPointBlockBudget_eq_pow (d : ℕ) :
    2 * allAffinePointBlockFeatureCount d = 2 ^ (2 * d + 1) := by
  calc
    2 * allAffinePointBlockFeatureCount d
        = 2 * (2 ^ d * 2 ^ d) := by
            rw [allAffinePointBlockFeatureCount_eq]
    _ = 2 * 2 ^ (d + d) := by
          rw [← Nat.pow_add]
    _ = 2 ^ 1 * 2 ^ (d + d) := by
          simp
    _ = 2 ^ (1 + (d + d)) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (2 * d + 1) := by
          simp [two_mul, Nat.add_assoc, Nat.add_comm]

/-- On `BitVec n`, the standard point-block sparse-threshold counting gap
forces sample size larger than the explicit point-block bit budget. -/
theorem sparseThresholdPointBlockBudgetPow_lt_sampleSize_of_gap_bitVec
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ m) :
    2 ^ (2 * (r + (k + k)) + 1) < m := by
  have hlt :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) < m :=
    sparseThresholdPointBlockBudget_lt_sampleSize_of_two_le_surfaceCard
      (Z := BitVec n) (r := r) (k := k) (m := m)
      (two_le_card_exactVisiblePostSwitchSurface_bitVec_of_width_pos
        (n := n) (k := k) hvis)
      hbound
  have hlt' :
      2 * (2 ^ (r + (k + k)) * 2 ^ (r + (k + k))) < m := by
    simpa [allAffinePointBlockFeatureCount_eq] using hlt
  have hbudget :
      2 * (2 ^ (r + (k + k)) * 2 ^ (r + (k + k))) =
        2 ^ (2 * (r + (k + k)) + 1) := by
    simpa [allAffinePointBlockFeatureCount_eq] using
      (sparseThresholdPointBlockBudget_eq_pow (d := r + (k + k)))
  exact hbudget ▸ hlt'

namespace ActualSwitchedLocalInterface

/-- Any surjective actual switched-local sparse-threshold ERM packet on
`BitVec n` that satisfies the current point-block counting-gap hypotheses
already needs sample size larger than `2^(2*(n + 2k) + 1)`.  This is a
conditional consequence of the current liveness packet, not an unconditional
closure theorem for the branch. -/
theorem visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict
    {Index : Type*} {Block : Type*}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {zfeat : BitVec n → BitVec r}
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          T
          zfeat))
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ m) :
    2 ^ (2 * (n + (k + k)) + 1) < m := by
  have hnr : n ≤ r := by
    by_contra hnr
    exact
      (not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_width_lt
        T zfeat hsurj (Nat.lt_of_not_ge hnr)) hdata
  have hroute :
      2 ^ (2 * (r + (k + k)) + 1) < m :=
    sparseThresholdPointBlockBudgetPow_lt_sampleSize_of_gap_bitVec
      (n := n) (r := r) (k := k) (m := m) hvis hbound
  have hmono :
      2 ^ (2 * (n + (k + k)) + 1) ≤
        2 ^ (2 * (r + (k + k)) + 1) := by
    exact
      Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
  exact lt_of_le_of_lt hmono hroute

/-- Any nontrivial full-rule actual switched-local sparse-threshold ERM packet
on `BitVec n` that satisfies the current point-block counting-gap hypotheses
already needs sample size larger than `2^(2*(n + 2k) + 1)`.  This is a
conditional consequence of the current liveness packet, not an unconditional
closure theorem for the branch. -/
theorem fullRuleActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData
    {zfeat : BitVec n → BitVec r}
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat))
    (hvis : 0 < n + (k + k))
    (_hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ m) :
    2 ^ (2 * (n + (k + k)) + 1) < m := by
  exact
    visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict
      (n := n) (r := r) (k := k) (m := m)
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      (zfeat := zfeat)
      hdata
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hvis
      hbound

end ActualSwitchedLocalInterface

end BitVec

end Mettapedia.Computability.PNP
