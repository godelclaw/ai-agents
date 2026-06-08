import Mettapedia.Computability.PNP.ActualSwitchedLocalERMConstruction

/-!
# Regression checks for the actual switched-local ERM construction

These checks keep the manuscript-shaped construction connected to the concrete
ZAB ERM small-image route.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}

theorem regression_exactZAB_ERM_construction_zab_data
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ZABDecisionListData
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples)
      zfeat :=
  exactZABDecisionListERMConstruction_zabDecisionListData
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat samples

noncomputable def regression_exactZAB_ERM_construction_bit_code_data
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    BitCodeData
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples)
      (r + 2 * k + 1) :=
  exactZABDecisionListERMConstruction_bitCodeData
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat samples

theorem regression_exactZAB_ERM_construction_cover
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) :=
  exactZABDecisionListERMConstruction_finitePredictorCover
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat samples

theorem regression_exactZAB_ERM_construction_payload
    [Fintype Z]
    {clock : ℕ}
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat samples).predictorFamily
      (r + 2 * k + 1) clock :=
  exactZABDecisionListERMConstruction_clockedKpolyFiniteLearningPayload
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat samples

theorem regression_bitVecZAB_ERM_construction_cover
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    (bitVecZABDecisionListERMConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf samples).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) :=
  bitVecZABDecisionListERMConstruction_finitePredictorCover
    (r := r) (k := k) (Index := Index) (Block := Block)
    zOf aOf bOf samples

theorem regression_bitVecZAB_ERM_construction_payload
    [Fintype (BitVec r)]
    {clock : ℕ}
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMConstruction
        (r := r) (k := k) (Index := Index) (Block := Block)
        zOf aOf bOf samples).predictorFamily
      (r + 2 * k + 1) clock :=
  bitVecZABDecisionListERMConstruction_clockedKpolyFiniteLearningPayload
    (r := r) (k := k) (Index := Index) (Block := Block)
    zOf aOf bOf samples

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
