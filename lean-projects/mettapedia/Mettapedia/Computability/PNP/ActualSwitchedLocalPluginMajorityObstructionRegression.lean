import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginMajorityObstruction

/-!
# Regression checks for the plug-in majority obstruction

These checks keep the counted-majority endpoint attached to the full
exact-visible family and to the negative small-image theorems.
-/

namespace Mettapedia.Computability.PNP

universe v

theorem regression_pluginMajority_surjective (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginMajorityActualSwitchedLocalInterface_surjective Z k

theorem regression_pluginMajority_no_small_cover
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  pluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    hs

theorem regression_pluginMajority_no_payload
    {Z : Type v} {k s clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

theorem regression_pluginMajority_no_zabDecisionListData
    {Z : Type v} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

end Mettapedia.Computability.PNP
