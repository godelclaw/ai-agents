import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryConcentrationObstruction
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.FinitePMFPointMassBound
import Mathlib.Tactic

/-!
# P vs NP route obstruction: recovery packets force near-uniform concentration

The earlier recovery concentration obstruction shows that on a surjective
actual-local sparse-threshold recovery packet, every visible point `y` must
satisfy `1 - μ y ≤ q`.

This file combines that fact with the finite pigeonhole bound that some point
must have mass at most the uniform mass `1 / |surface|`.  Therefore every
surjective recovery packet on a finite nonempty exact visible surface forces

* `1 - |surface|⁻¹ ≤ q`.

On the full-rule `BitVec n` endpoint this specializes to

* `1 - 2^-(n + 2*k) ≤ q`.

So the recovery-side agreement threshold must already be extremely close to `1`
once the visible exact surface is large.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- On a finite nonempty exact visible surface, every surjective actual-local
sparse-threshold recovery packet forces `q` to be at least the complement of
the uniform point mass. -/
theorem one_sub_inv_card_le_of_surjective_predict
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹ ≤ q := by
  obtain ⟨y, hy⟩ := PMF.exists_apply_le_inv_card μ
  exact le_trans
    (tsub_le_tsub_left hy 1)
    (h.one_sub_apply_le_of_surjective_predict hsurj y)

end SharedExactZABSparseThresholdERMRecoveryData

/-- Therefore no surjective actual-local sparse-threshold recovery packet can
exist below the uniform-complement threshold `1 - |surface|⁻¹`. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_inv_card
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hq_lt :
      q < 1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_lt_of_ge (h.one_sub_inv_card_le_of_surjective_predict hsurj) hq_lt

/-- The same obstruction lifts to the bounded-sample plug-in-majority
manuscript-facing endpoint once the sample bound is large enough for
surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_inv_card
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {sampleBound : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hq_lt :
      q < 1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_inv_card
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      zfeat
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)
      hq_lt

/-- In particular, the full-rule actual-local endpoint is impossible below the
same uniform-complement threshold. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_inv_card
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {zfeat : Z → BitVec r}
    (hq_lt :
      q < 1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_inv_card
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hq_lt

/-- Equivalently, any nonempty full-rule actual-local sparse-threshold recovery
packet forces `q` above the uniform-complement threshold. -/
theorem one_sub_inv_card_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {zfeat : Z → BitVec r}
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      q) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    h.one_sub_inv_card_le_of_surjective_predict
      (fullRuleActualSwitchedLocalInterface_surjective Z k)

end Abstract

section BitVec

variable {n k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {q : ℝ≥0∞} {zfeat : BitVec n → BitVec r}

local instance exactVisiblePostSwitchSurfaceNonemptyBitVec :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

/-- On the full-rule `BitVec n` endpoint, the recovery threshold must be at
least `1 - 2^-(n + 2*k)`. -/
theorem one_sub_pow_inv_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      q) :
    1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹ ≤ q := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    (one_sub_inv_card_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
      (μ := μ)
      (Z := BitVec n)
      (k := k)
      (zfeat := zfeat)
      h)

/-- Therefore the full-rule `BitVec n` endpoint is impossible below the same
uniform-complement threshold. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    (hq_lt : q < 1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact not_lt_of_ge
    (one_sub_pow_inv_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
      (μ := μ)
      (k := k)
      (zfeat := zfeat)
      h)
    hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
