import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveRegionObstruction
import Mettapedia.Computability.PNP.FinitePMFHeavyRegionCharacterization

/-!
# P vs NP route characterization: surjective recovery heavy-region obstructions
  collapse to the lightest-point threshold

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveRegionObstruction`
showed that if the actual switched family is already surjective onto all Boolean
rules on the exact visible surface, then every proper finite visible region has
mass at most `q`.

This file packages the intrinsic content of that surjective obstruction.  On a
finite PMF, the sharp proper-region threshold is already

* `1 - μ (lightestPoint μ)`.

So on the surjective branch, the whole proper-region search collapses to the
complement of one lightest visible point, even when the realized family is not
injectively indexed.
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

/-- On the surjective branch, the recovery packet already enforces the whole
proper-region mass family. -/
theorem allProperRegionMass_le_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ∀ region : Finset (ExactVisiblePostSwitchSurface Z k),
      (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) →
        region.sum (fun x => μ x) ≤ q := by
  intro region hout
  exact h.regionMass_le_of_surjective_predict_of_exists_not_mem hsurj region hout

/-- Therefore the surjective branch already forces `q` above the complement
mass of the lightest visible point. -/
theorem one_sub_apply_lightestPoint_le_of_surjective_predict
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  classical
  exact
    (PMF.allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
      (μ := μ) (q := q)).1 <|
      h.allProperRegionMass_le_of_surjective_predict hsurj

end SharedExactZABSparseThresholdERMRecoveryData

/-- So on the surjective branch, falling below the lightest-point threshold is
already impossible. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_lt_of_ge
    (h.one_sub_apply_lightestPoint_le_of_surjective_predict hsurj)
    hq_lt

/-- The same lightest-point obstruction lifts to the bounded-sample
plug-in-majority endpoint once the sample bound is large enough for
surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {sampleBound : ℕ}
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      (zfeat := zfeat)
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)
      hq_lt

/-- In particular, the full-rule actual-local endpoint is already impossible
below the same lightest-point threshold. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      (zfeat := zfeat)
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hq_lt

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
