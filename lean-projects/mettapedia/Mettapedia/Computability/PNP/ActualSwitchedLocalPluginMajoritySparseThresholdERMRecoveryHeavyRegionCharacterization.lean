import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoverySurjectiveHeavyRegionCharacterization

/-!
# PNP crux: counted plug-in majority does not escape the lightest-point
  recovery threshold

`ActualSwitchedLocalPluginMajorityObstruction` already proves that unrestricted
counted plug-in majority is surjective onto every Boolean rule on the exact
visible post-switch surface.

This file transfers the sharper `q`-dependent recovery obstruction to that
endpoint.  Since counted plug-in majority is still just a surjective
actual-local family, any hypothetical sparse-threshold recovery packet already
forces

* `1 - μ (PMF.lightestPoint μ) ≤ q`.

So the route cannot rescue unrestricted counted-majority local rules by moving
from visible-budget contradictions to a later recovery-only threshold claim.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}

/-- Because unrestricted counted plug-in majority is surjective on the full
exact-visible rule family, any hypothetical sparse-threshold recovery packet
already forces `q` above the lightest-point complement mass. -/
theorem pluginMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginMajorityActualSwitchedLocalInterface Z k)
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  rcases h with ⟨h⟩
  exact
    h.one_sub_apply_lightestPoint_le_of_surjective_predict
      (pluginMajorityActualSwitchedLocalInterface_surjective Z k)

/-- Therefore unrestricted counted plug-in majority cannot carry the shared
sparse-threshold recovery packet below the same lightest-point threshold. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginMajorityActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := pluginMajorityActualSwitchedLocalInterface Z k)
      (zfeat := zfeat)
      (pluginMajorityActualSwitchedLocalInterface_surjective Z k)
      hq_lt

end Abstract

end Mettapedia.Computability.PNP
