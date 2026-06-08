import Mettapedia.Computability.PNP.ActualSwitchedLocalCodeConstruction

/-!
# Regression checks for the actual switched-local ZAB code construction

These checks protect the concrete route where a manuscript supplies one
bounded ZAB decision-list code per output index.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}

theorem regression_exactZAB_code_construction_zab_data
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ZABDecisionListData
      (exactZABCodeConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat codes)
      zfeat :=
  exactZABCodeConstruction_zabDecisionListData
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat codes

noncomputable def regression_exactZAB_code_construction_bit_code_data
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    BitCodeData
      (exactZABCodeConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat codes)
      (r + 2 * k + 1) :=
  exactZABCodeConstruction_bitCodeData
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat codes

theorem regression_exactZAB_code_construction_cover
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (exactZABCodeConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) :=
  exactZABCodeConstruction_finitePredictorCover
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat codes

theorem regression_exactZAB_code_construction_payload
    [Fintype Z]
    {clock : ℕ}
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ClockedKpolyFiniteLearningPayload
      (exactZABCodeConstruction
        (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
        zOf aOf bOf zfeat codes).predictorFamily
      (r + 2 * k + 1) clock :=
  exactZABCodeConstruction_clockedKpolyFiniteLearningPayload
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat codes

theorem regression_bitVecZAB_code_construction_cover
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (bitVecZABCodeConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf codes).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) :=
  bitVecZABCodeConstruction_finitePredictorCover
    (r := r) (k := k) (Index := Index) (Block := Block)
    zOf aOf bOf codes

theorem regression_bitVecZAB_code_construction_payload
    [Fintype (BitVec r)]
    {clock : ℕ}
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABCodeConstruction
        (r := r) (k := k) (Index := Index) (Block := Block)
        zOf aOf bOf codes).predictorFamily
      (r + 2 * k + 1) clock :=
  bitVecZABCodeConstruction_clockedKpolyFiniteLearningPayload
    (r := r) (k := k) (Index := Index) (Block := Block)
    zOf aOf bOf codes

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
