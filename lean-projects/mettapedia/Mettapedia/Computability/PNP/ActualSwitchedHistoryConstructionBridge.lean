import Mettapedia.Computability.PNP.ActualSwitchedHistoryWrapper
import Mettapedia.Computability.PNP.ActualSwitchedLocalERMConstruction

/-!
# PNP route bridge: switched-history wrappers from concrete local packets

The remaining switched-history route is now a one-family wrapper theorem.  This
file packages the positive side of that interface for the direct exact ZAB ERM
construction already formalized in the library.

Once the actual switched family is instantiated by this ERM construction, the
switched-history exact-visible and clocked wrappers are immediate.  The
fielded switching premise no longer carries any independent positive work.
-/

namespace Mettapedia.Computability.PNP

universe x u v w

namespace ActualSwitchedLocalInterface

section ERMConstruction

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}

theorem exactZABDecisionListERMConstruction_switchedHistoryExactVisibleCompressionWrapper
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    {Ω : Type x} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    SwitchedHistoryExactVisibleCompressionWrapper
      Ω
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples)
      (r + 2 * k + 1)
      hist
      items := by
  exact
    (exactZABDecisionListERMConstruction_zabDecisionListData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).switchedHistoryExactVisibleCompressionWrapper

theorem exactZABDecisionListERMConstruction_switchedHistoryClockedKpolyFiniteLearningWrapper
    [Fintype Z]
    {clock : ℕ}
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    {Ω : Type x} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper
      Ω
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples)
      (r + 2 * k + 1)
      clock
      hist
      items := by
  exact
    (exactZABDecisionListERMConstruction_zabDecisionListData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).switchedHistoryClockedKpolyFiniteLearningWrapper

end ERMConstruction

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
