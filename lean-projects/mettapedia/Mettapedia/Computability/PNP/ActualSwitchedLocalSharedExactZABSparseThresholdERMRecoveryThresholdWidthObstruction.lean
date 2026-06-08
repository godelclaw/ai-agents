import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryCardinalityObstruction
import Mathlib.Tactic

/-!
# P vs NP route obstruction: small recovery thresholds force small visible width

The recovery-cardinality obstruction already proves that every surjective
actual-local sparse-threshold recovery packet on the full-rule `BitVec n`
surface must satisfy

* `1 - 2^-(n + 2*k) ≤ q`.

This file inverts that inequality.  If a route claims a stricter recovery
threshold

* `q < 1 - 2^-p`,

then Lean forces the visible width to satisfy

* `n + 2*k < p`.

So any manuscript endpoint with a concrete `q` bound below `1 - 2^-p` already
faces a direct visible-width obstruction.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

/-- The thresholds `1 - 2^-p` are monotone in `p`. -/
theorem one_sub_pow_inv_monotone {p m : ℕ} (hpm : p ≤ m) :
    1 - (2 ^ p : ℝ≥0∞)⁻¹ ≤ 1 - (2 ^ m : ℝ≥0∞)⁻¹ := by
  have hpow_nat : 2 ^ p ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hpm
  have hpow : (2 ^ p : ℝ≥0∞) ≤ (2 ^ m : ℝ≥0∞) := by
    exact_mod_cast hpow_nat
  exact tsub_le_tsub_left (ENNReal.inv_le_inv' hpow) 1

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {q : ℝ≥0∞} {zfeat : BitVec n → BitVec r}

/-- If a full-rule `BitVec n` recovery packet exists below the threshold
`1 - 2^-p`, then the exact visible width must satisfy `n + 2*k < p`. -/
theorem visibleWidth_lt_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {p : ℕ}
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      q)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    n + 2 * k < p := by
  by_contra hnot
  have hle : p ≤ n + 2 * k := Nat.not_lt.mp hnot
  have hbound : 1 - (2 ^ p : ℝ≥0∞)⁻¹ ≤ q := by
    exact le_trans
      (one_sub_pow_inv_monotone hle)
      (one_sub_pow_inv_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
        (μ := μ)
        (k := k)
        (zfeat := zfeat)
        h)
  exact not_lt_of_ge hbound hq_lt

/-- Therefore a full-rule `BitVec n` recovery packet is impossible below
`1 - 2^-p` whenever `p ≤ n + 2*k`. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
    {p : ℕ}
    (hwidth : p ≤ n + 2 * k)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_lt_of_ge hwidth <|
    visibleWidth_lt_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (zfeat := zfeat)
      h
      hq_lt

/-- The same width obstruction lifts to the bounded-sample plug-in-majority
endpoint once the sample bound is large enough for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {sampleBound p : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      zfeat
      q)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    n + 2 * k < p := by
  letI : Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k) :=
    ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩
  by_contra hnot
  have hle : p ≤ n + 2 * k := Nat.not_lt.mp hnot
  have hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface
          (BitVec n) k sampleBound).predictorFamily.predict :=
    boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
      (Z := BitVec n) k sampleBound hsample
  have hcard : 1 - (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) : ℝ≥0∞)⁻¹ ≤ q := by
    exact h.one_sub_inv_card_le_of_surjective_predict hsurj
  have hbound : 1 - (2 ^ p : ℝ≥0∞)⁻¹ ≤ q := by
    exact le_trans
      (one_sub_pow_inv_monotone hle)
      (by simpa [card_exactVisiblePostSwitchSurface_bitVec] using hcard)
  exact not_lt_of_ge hbound hq_lt

/-- Therefore the bounded-sample plug-in-majority endpoint is impossible below
`1 - 2^-p` whenever `p ≤ n + 2*k`. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
    {sampleBound p : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hwidth : p ≤ n + 2 * k)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_lt_of_ge hwidth <|
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      hsample
      h
      hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
