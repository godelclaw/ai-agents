import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveHeavyRegionCharacterization

/-!
# PNP crux: unrestricted sample-level plug-in majority does not escape the
  lightest-point recovery threshold

`ActualSwitchedLocalPluginSampleMajorityObstruction` already proves that the
unrestricted sample-level plug-in majority endpoint is surjective onto every
Boolean rule on the exact visible post-switch surface.

This file transfers the sharper `q`-dependent recovery obstruction to that
endpoint.  Since unrestricted sample-level plug-in majority is still just a
surjective actual-local family, any hypothetical sparse-threshold recovery
packet already forces

* `1 - μ (PMF.lightestPoint μ) ≤ q`.

So the route cannot rescue unrestricted sample-level plug-in majority by
leaving the visible-budget regime and appealing only to the later recovery
threshold.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}

/-- Because unrestricted sample-level plug-in majority is surjective on the
full exact-visible rule family, any hypothetical sparse-threshold recovery
packet already forces `q` above the lightest-point complement mass. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  rcases h with ⟨h⟩
  exact
    h.one_sub_apply_lightestPoint_le_of_surjective_predict
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)

/-- Therefore unrestricted sample-level plug-in majority cannot carry the
shared sparse-threshold recovery packet below the same lightest-point
threshold. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := pluginSampleMajorityActualSwitchedLocalInterface Z k)
      (zfeat := zfeat)
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)
      hq_lt

end Abstract

end Mettapedia.Computability.PNP
