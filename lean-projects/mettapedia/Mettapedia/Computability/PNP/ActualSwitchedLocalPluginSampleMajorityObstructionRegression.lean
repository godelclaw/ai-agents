import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajorityObstruction

/-!
# Regression checks for the sample-level plug-in majority obstruction

These checks keep the actual finite-sample majority endpoint attached to the
full exact-visible Boolean rule family.  They also preserve the precise
negative consequences for the current small-image bridge targets.
-/

namespace Mettapedia.Computability.PNP.PluginSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example (Z : Type) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k

example {Z : Type} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

example {Z : Type} {k s clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

example {Z : Type} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) s) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

example {Z : Type} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    (Z := Z) (k := k) (r := r) zfeat hs

end Mettapedia.Computability.PNP.PluginSampleMajorityObstructionRegression
