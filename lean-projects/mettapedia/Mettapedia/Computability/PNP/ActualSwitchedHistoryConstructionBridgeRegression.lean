import Mettapedia.Computability.PNP.ActualSwitchedHistoryConstructionBridge

/-!
# Regression checks for switched-history construction bridges

These checks keep the positive switched-history route tied to the direct exact
ZAB ERM construction already formalized in Lean.
-/

namespace Mettapedia.Computability.PNP

universe x u v w

namespace ActualSwitchedLocalInterface

section ERMConstruction

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}
variable {Ω : Type x} [Fintype Ω]
variable {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}

theorem regression_exactZABDecisionListERMConstruction_switchedHistoryExactVisibleCompressionWrapper
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SwitchedHistoryExactVisibleCompressionWrapper
      Ω
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples)
      (r + 2 * k + 1)
      hist
      items := by
  exact
    exactZABDecisionListERMConstruction_switchedHistoryExactVisibleCompressionWrapper
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples

theorem regression_exactZABDecisionListERMConstruction_switchedHistoryClockedKpolyFiniteLearningWrapper
    [Fintype Z]
    {clock : ℕ}
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
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
    exactZABDecisionListERMConstruction_switchedHistoryClockedKpolyFiniteLearningWrapper
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      (clock := clock)
      zOf aOf bOf zfeat samples

end ERMConstruction

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
