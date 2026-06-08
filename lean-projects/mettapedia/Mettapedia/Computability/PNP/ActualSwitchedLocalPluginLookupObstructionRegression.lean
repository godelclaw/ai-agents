import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginLookupObstruction

/-!
# Regression checks for the plug-in lookup obstruction

These checks keep the manuscript-facing plug-in lookup endpoint attached to the
full exact-visible family and to the negative small-image theorems.
-/

namespace Mettapedia.Computability.PNP

universe v

theorem regression_pluginLookup_surjective (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginLookupActualSwitchedLocalInterface_surjective Z k

theorem regression_pluginLookup_no_small_cover
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  pluginLookupActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard hs

theorem regression_pluginLookup_no_bitCodeData
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (pluginLookupActualSwitchedLocalInterface Z k) s) :=
  pluginLookupActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard hs

theorem regression_pluginLookup_no_zabDecisionListData
    {Z : Type v} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) :=
  pluginLookupActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

end Mettapedia.Computability.PNP
