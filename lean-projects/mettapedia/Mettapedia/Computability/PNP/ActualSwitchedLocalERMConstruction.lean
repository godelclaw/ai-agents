import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure

/-!
# PNP grassroots: actual switched-local ERM construction

This file records the concrete construction that the narrowed actual-local
route needs.  Given the manuscript visible-data maps `zOf`, `aOf`, and `bOf`,
plus an indexed sample assignment, we build an `ActualSwitchedLocalInterface`
whose local rule family is definitionally the exact ZAB decision-list ERM
family.  Therefore the already-proved `ZABDecisionListData` and `BitCodeData`
contracts apply without adding another structural assumption.

The remaining manuscript burden is no longer a generic small-image lemma: it is
to show that the paper's switched family is this ERM construction, or supplies
the same per-index ZAB decision-list codes.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k r : ℕ} {Index : Type u} {Block : Type w}

/-- The concrete actual switched-local family induced by ERM over the shared
`(zfeat z, a, b)` ZAB decision-list class.  The maps `zOf`, `aOf`, and `bOf`
are exactly the visible-data maps from the manuscript local-normal-form
bracket; the non-arbitrary content is that every local rule is selected by the
same fixed ERM family. -/
noncomputable def exactZABDecisionListERMConstruction
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ActualSwitchedLocalInterface Z k Index Block where
  zOf := zOf
  aOf := aOf
  bOf := bOf
  localRule :=
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).predict
  output := fun i phi =>
    (exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).predict
      i ⟨zOf phi, aOf i phi, bOf phi⟩
  output_eq_local := by
    intro i phi
    rfl

@[simp] theorem exactZABDecisionListERMConstruction_predictorFamily
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples := by
  rfl

/-- The concrete actual switched-local ERM construction satisfies the ZAB
decision-list data contract. -/
noncomputable def exactZABDecisionListERMConstruction_zabDecisionListData
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
  zabDecisionListData_of_eq_exactZABDecisionListERMFamily
    (Z := Z) (k := k) (Index := Index) (Block := Block)
    (exactZABDecisionListERMConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples)
    zfeat samples
    (exactZABDecisionListERMConstruction_predictorFamily
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples)

/-- The same construction satisfies the bounded-bit-code data contract at the
normalized visible ZAB budget. -/
noncomputable def exactZABDecisionListERMConstruction_bitCodeData
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
  bitCodeData_of_eq_exactZABDecisionListERMFamily
    (Z := Z) (k := k) (Index := Index) (Block := Block)
    (exactZABDecisionListERMConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples)
    zfeat samples
    (exactZABDecisionListERMConstruction_predictorFamily
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples)

/-- Concrete small-image theorem for the actual switched-local ERM
construction. -/
theorem exactZABDecisionListERMConstruction_finitePredictorCover
    (zOf : Block → Z)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    (exactZABDecisionListERMConstruction
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    (exactZABDecisionListERMConstruction_zabDecisionListData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).finitePredictorCover

/-- Concrete clocked finite-learning payload for the actual switched-local ERM
construction. -/
theorem exactZABDecisionListERMConstruction_clockedKpolyFiniteLearningPayload
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
      (r + 2 * k + 1) clock := by
  exact
    (exactZABDecisionListERMConstruction_bitCodeData
      (Z := Z) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf zfeat samples).clockedKpolyFiniteLearningPayload

/-- Bit-valued specialization where the manuscript latent feature is already
the visible `r`-bit vector. -/
noncomputable def bitVecZABDecisionListERMConstruction
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ActualSwitchedLocalInterface (BitVec r) k Index Block :=
  exactZABDecisionListERMConstruction
    (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
    zOf aOf bOf identityZExtractor samples

@[simp] theorem bitVecZABDecisionListERMConstruction_predictorFamily
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    (bitVecZABDecisionListERMConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf samples).predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples := by
  rfl

/-- Bit-valued concrete small-image theorem for the actual switched-local ERM
construction. -/
theorem bitVecZABDecisionListERMConstruction_finitePredictorCover
    (zOf : Block → BitVec r)
    (aOf : Index → Block → BitVec k)
    (bOf : Block → BitVec k)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    (bitVecZABDecisionListERMConstruction
      (r := r) (k := k) (Index := Index) (Block := Block)
      zOf aOf bOf samples).predictorFamily.FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    exactZABDecisionListERMConstruction_finitePredictorCover
      (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf identityZExtractor samples

/-- Bit-valued concrete clocked finite-learning payload for the actual
switched-local ERM construction. -/
theorem bitVecZABDecisionListERMConstruction_clockedKpolyFiniteLearningPayload
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
      (r + 2 * k + 1) clock := by
  exact
    exactZABDecisionListERMConstruction_clockedKpolyFiniteLearningPayload
      (Z := BitVec r) (k := k) (r := r) (Index := Index) (Block := Block)
      zOf aOf bOf identityZExtractor samples

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
