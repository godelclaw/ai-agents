import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryThresholdWidthObstruction
import Mathlib.Tactic

/-!
# P vs NP route obstruction: small recovery thresholds tighten the visible budget

`ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction`
already gives the unconditional surjective width ceiling

* `n ≤ 2*r + 2*k + 1`.

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryThresholdWidthObstruction`
adds that any recovery threshold below `1 - 2^-p` forces

* `n + 2*k < p`.

This file combines those arithmetic patterns at the point-block boundary.  If a
route claims the stricter recovery estimate

* `q < 1 - 2^-(2*r + 4*k + slack + 1)`,

then Lean improves the visible-width ceiling to

* `n ≤ 2*r + 2*k + slack`.

So in particular the former boundary case `n = 2*r + 2*k + 1` is impossible
once `q < 1 - 2^-(2*r + 4*k + 1)`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {q : ℝ≥0∞} {zfeat : BitVec n → BitVec r}

/-- A recovery threshold below the point-block boundary value
`1 - 2^-(2*r + 4*k + slack + 1)` improves the full-rule visible-width ceiling
to `n ≤ 2*r + 2*k + slack`. -/
theorem visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {slack : ℕ}
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      q)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    n ≤ 2 * r + 2 * k + slack := by
  have hlt :
      n + 2 * k < 2 * r + 4 * k + slack + 1 := by
    exact
      visibleWidth_lt_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
        (μ := μ)
        (k := k)
        (zfeat := zfeat)
        (p := 2 * r + 4 * k + slack + 1)
        h
        hq_lt
  omega

/-- Therefore the full-rule endpoint is impossible once the visible width
exceeds that sharpened point-block budget. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
    {slack : ℕ}
    (hgap : 2 * r + 2 * k + slack < n)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hgap <|
    visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (zfeat := zfeat)
      (slack := slack)
      h
      hq_lt

/-- The same sharpened visible-width ceiling lifts to bounded-sample
plug-in-majority once the sample bound is large enough for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {sampleBound slack : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      zfeat
      q)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    n ≤ 2 * r + 2 * k + slack := by
  have hlt :
      n + 2 * k < 2 * r + 4 * k + slack + 1 := by
    exact
      boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
        (μ := μ)
        (k := k)
        (sampleBound := sampleBound)
        (zfeat := zfeat)
        (p := 2 * r + 4 * k + slack + 1)
        hsample
        h
        hq_lt
  omega

/-- Therefore the bounded-sample plug-in-majority endpoint is impossible once
the visible width exceeds that sharpened point-block budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
    {sampleBound slack : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hgap : 2 * r + 2 * k + slack < n)
    (hq_lt : q < 1 - (2 ^ (2 * r + 4 * k + slack + 1) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hgap <|
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      (slack := slack)
      hsample
      h
      hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
