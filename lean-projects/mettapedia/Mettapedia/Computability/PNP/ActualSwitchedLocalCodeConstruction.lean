import Mettapedia.Computability.PNP.ActualSwitchedLocalERMConstruction
import Mettapedia.Computability.PNP.CanonicalZABCodeWitness

/-!
# PNP grassroots: actual switched-local ZAB code construction

`ActualSwitchedLocalERMConstruction` covers the case where the manuscript local
rules are selected by ERM over the shared `(zfeat z, a, b)` decision-list class.
This file covers the other exact route left open there: if the manuscript
supplies one concrete ZAB decision-list code for each index, then the actual
switched-local family built from those codes has the required finite predictor
image and clocked payload.

This is still a construction theorem, not a new broad assumption.  The only
remaining burden for a manuscript-specific family is to identify its local
rules with the `codes` used here.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}

/-- The concrete actual switched-local family induced by an explicit assignment
of one shared `(zfeat z, a, b)` ZAB decision-list code to each output index. -/
noncomputable def exactZABCodeConstruction
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ActualSwitchedLocalInterface Z k Index Block where
  zOf := zOf
  aOf := aOf
  bOf := bOf
  localRule :=
    (canonicalZABCodeFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes).predict
  output := fun i phi =>
    rawExactZABDecisionListPredict
      (Z := Z) (r := r) (k := k) zfeat (codes i)
      ⟨zOf phi, aOf i phi, bOf phi⟩
  output_eq_local := by
    intro i phi
    rfl

@[simp] theorem exactZABCodeConstruction_predictorFamily
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (exactZABCodeConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes).predictorFamily =
        canonicalZABCodeFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat codes := by
  rfl

/-- The explicit-code construction satisfies the ZAB decision-list data
contract. -/
noncomputable def exactZABCodeConstruction_zabDecisionListData
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
  zabDecisionListDataOfCodes
    (Z := Z) (k := k) (Index := Index) (Block := Block)
    (exactZABCodeConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes)
    zfeat codes
    (by
      intro i
      rfl)

/-- The explicit-code construction satisfies the bounded-code data contract at
the normalized visible ZAB budget. -/
noncomputable def exactZABCodeConstruction_bitCodeData
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
  (exactZABCodeConstruction_zabDecisionListData
    (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf zfeat codes).bitCodeData

/-- Concrete small-image theorem for the actual switched-local code
construction. -/
theorem exactZABCodeConstruction_finitePredictorCover
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (exactZABCodeConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    (exactZABCodeConstruction_zabDecisionListData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes).finitePredictorCover

/-- Concrete clocked finite-learning payload for the actual switched-local code
construction. -/
theorem exactZABCodeConstruction_clockedKpolyFiniteLearningPayload
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
      (r + 2 * k + 1) clock := by
  exact
    (exactZABCodeConstruction_bitCodeData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat codes).clockedKpolyFiniteLearningPayload

/-- Bit-valued specialization of the explicit-code construction. -/
noncomputable def bitVecZABCodeConstruction
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    ActualSwitchedLocalInterface (BitVec r) k Index Block :=
  exactZABCodeConstruction
    (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf identityZExtractor codes

@[simp] theorem bitVecZABCodeConstruction_predictorFamily
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (bitVecZABCodeConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf codes).predictorFamily =
        canonicalZABCodeFamily
          (Z := BitVec r) (r := r) (k := k) (Index := Index)
          identityZExtractor codes := by
  rfl

/-- Bit-valued concrete small-image theorem for the actual switched-local code
construction. -/
theorem bitVecZABCodeConstruction_finitePredictorCover
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k))) :
    (bitVecZABCodeConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf codes).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    exactZABCodeConstruction_finitePredictorCover
      (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf identityZExtractor codes

/-- Bit-valued concrete clocked finite-learning payload for the actual
switched-local code construction. -/
theorem bitVecZABCodeConstruction_clockedKpolyFiniteLearningPayload
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
      (r + 2 * k + 1) clock := by
  exact
    exactZABCodeConstruction_clockedKpolyFiniteLearningPayload
      (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf identityZExtractor codes

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
