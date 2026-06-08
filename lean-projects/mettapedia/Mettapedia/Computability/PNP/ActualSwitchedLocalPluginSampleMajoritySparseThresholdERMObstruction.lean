import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryVisibleBudgetObstruction

/-!
# PNP crux: unrestricted sample-level plug-in majority still cannot be treated
  as the shared sparse-threshold ERM route

`ActualSwitchedLocalPluginSampleMajorityObstruction` already shows that the
sample-level plug-in majority endpoint is surjective onto every Boolean rule on
the exact visible post-switch surface: the graph sample of a rule recovers that
rule pointwise.

This file turns that expressivity fact against a stronger manuscript-facing
identification claim.  If one now tries to say that the same endpoint is
actually one shared exact sparse-threshold ERM family on the point-block basis,
or even carries the stronger sparse-threshold recovery packet, then the
existing visible-budget obstruction applies immediately.

So "finite sample plus empirical majority" does not by itself land inside the
already-analyzed sparse-threshold ERM route.  That identification still owes a
separate theorem.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ}

/-- The unrestricted sample-level plug-in majority endpoint cannot be the
manuscript-facing shared exact sparse-threshold ERM family below the point-
block visible-budget threshold. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
      (T := pluginSampleMajorityActualSwitchedLocalInterface Z k)
      zfeat
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)
      hs

/-- The stronger manuscript-facing sparse-threshold recovery packet is likewise
impossible on the unrestricted sample-level plug-in majority endpoint below the
same visible-budget threshold. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_surfaceCard
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hs <|
    h.surfaceCard_le_of_surjective_predict
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)

end Abstract

section BitVec

variable {n k r : ℕ}

/-- On `BitVec n`, any sample-level plug-in majority endpoint identified with
one shared exact sparse-threshold ERM family must satisfy the same
unconditional half-width ceiling as the full-rule actual-local counterexample.
-/
theorem pluginSampleMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective (BitVec n) k)

/-- Therefore the unrestricted sample-level plug-in majority endpoint cannot be
identified with the manuscript-facing shared exact sparse-threshold ERM family
once `2*r + 2*k + 1 < n`. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

/-- The stronger manuscript-facing sparse-threshold recovery packet inherits
the same half-width obstruction on the unrestricted sample-level plug-in
majority endpoint. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective (BitVec n) k)

/-- Therefore the unrestricted sample-level plug-in majority endpoint cannot
carry the stronger sparse-threshold recovery packet below the same half-width
threshold. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
      (μ := μ)
      (zfeat := zfeat)
      (q := q)
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

end BitVec

end Mettapedia.Computability.PNP
