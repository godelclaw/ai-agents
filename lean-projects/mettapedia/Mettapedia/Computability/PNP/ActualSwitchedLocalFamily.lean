import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure

/-!
# PNP grassroots: the actual switched local family interface

The manuscript's switched local normal form has the shape

`output i phi = h_i (z phi, a_i phi, b phi)`.

This file records that shape directly, with the visible local input
`u = (z, a, b)` supplied from an actual block `phi` and output index `i`.
It then separates two facts:

* if the resulting exact-visible predictor family is identified with the
  concrete ZAB decision-list ERM family, the current clocked `Kpoly` finite
  learning payload closes;
* the locality shape alone is insufficient, because it still permits the full
  Boolean rule family on the exact visible surface.
-/

namespace Mettapedia.Computability.PNP

universe u v w

/-- A manuscript-shaped switched local family.  The block `phi` supplies the
local data `(z phi, a_i phi, b phi)` for each output index `i`, and the actual
output is required to agree with the selected local rule on that exact visible
input. -/
structure ActualSwitchedLocalInterface
    (Z : Type v) (k : ℕ) (Index : Type u) (Block : Type w) where
  zOf : Block → Z
  aOf : Index → Block → BitVec k
  bOf : Block → BitVec k
  localRule : Index → ExactVisiblePostSwitchSurface Z k → Bool
  output : Index → Block → Bool
  output_eq_local :
    ∀ i phi, output i phi = localRule i ⟨zOf phi, aOf i phi, bOf phi⟩

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- The exact visible input used by the actual switched local rule for output
index `i` on block `phi`. -/
def visibleInput
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    ExactVisiblePostSwitchSurface Z k :=
  ⟨T.zOf phi, T.aOf i phi, T.bOf phi⟩

@[simp] theorem visibleInput_z
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    (T.visibleInput i phi).z = T.zOf phi := rfl

@[simp] theorem visibleInput_a
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    (T.visibleInput i phi).a = T.aOf i phi := rfl

@[simp] theorem visibleInput_b
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    (T.visibleInput i phi).b = T.bOf phi := rfl

/-- The exact-visible predictor family selected by the local rules. -/
def predictorFamily
    (T : ActualSwitchedLocalInterface Z k Index Block) :
    ExactVisibleSwitchedFamily Z k Index where
  predict := T.localRule

@[simp] theorem predictorFamily_predict
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (i : Index) (u : ExactVisiblePostSwitchSurface Z k) :
    T.predictorFamily.predict i u = T.localRule i u := rfl

/-- The local-normal-form equation, stated using `visibleInput`. -/
theorem output_eq_visibleInput
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    T.output i phi = T.localRule i (T.visibleInput i phi) :=
  T.output_eq_local i phi

/-- If the actual switched local family is identified with the concrete
`(zfeat z, a, b)` decision-list ERM family, the clocked finite-learning payload
closes at the corresponding bit budget. -/
theorem clockedKpolyFiniteLearningPayload_of_eq_exactZABDecisionListERMFamily
    [Fintype Z]
    {r clock : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    Mettapedia.Computability.PNP.clockedKpolyFiniteLearningPayload_of_eq_exactZABDecisionListERMFamily
      (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
      zfeat samples hT

/-- Raw bit-valued version of the same closure theorem.  This is the precise
small-image assumption needed by the current bit-valued ZAB route: the actual
local-rule family must be the ERM-selected ZAB decision-list family. -/
theorem clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily
    {r clock : ℕ}
    [Fintype (BitVec r)]
    (T : ActualSwitchedLocalInterface (BitVec r) k Index Block)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    Mettapedia.Computability.PNP.clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (clock := clock) (Index := Index)
      samples hT

end ActualSwitchedLocalInterface

section FullRuleCounterexample

variable (Z : Type v) (k : ℕ)

/-- The manuscript local-normal-form interface still permits the full Boolean
rule family: take blocks to be exact visible inputs and let each index be the
local rule itself. -/
def fullRuleActualSwitchedLocalInterface :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun rule u => rule u
  output := fun rule u => rule u
  output_eq_local := by
    intro rule u
    rfl

@[simp] theorem fullRuleActualSwitchedLocalInterface_predictorFamily :
    (fullRuleActualSwitchedLocalInterface Z k).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

theorem fullRuleActualSwitchedLocalInterface_surjective :
    Function.Surjective
      (fullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  simpa using fullExactVisibleRuleFamily_surjective Z k

variable {Z k}

/-- The full-rule actual local interface has no finite predictor cover below
the exact visible truth-table budget. -/
theorem fullRuleActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (fullRuleActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  simpa using
    (fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)

/-- Consequently, the full-rule actual local interface refutes the clocked
finite-learning payload below the exact visible truth-table budget. -/
theorem fullRuleActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (fullRuleActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  simpa using
    (fullExactVisibleRuleFamily_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs)

/-- Therefore the present actual-locality interface alone cannot imply the
small finite predictor-image theorem for every switched local family. -/
theorem actualSwitchedLocalInterface_not_forall_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} {Block : Type v}
        (T : ActualSwitchedLocalInterface Z k Index Block),
        T.predictorFamily.FinitePredictorCover (2 ^ s)) := by
  intro hforall
  exact
    fullRuleActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs
      (hforall
        (Index := ExactVisibleRule Z k)
        (Block := ExactVisiblePostSwitchSurface Z k)
        (fullRuleActualSwitchedLocalInterface Z k))

/-- Therefore the present actual-locality interface alone cannot imply the
clocked finite-learning payload for every switched local family. -/
theorem actualSwitchedLocalInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} {Block : Type v}
        (T : ActualSwitchedLocalInterface Z k Index Block),
        ClockedKpolyFiniteLearningPayload T.predictorFamily s clock) := by
  intro hforall
  exact
    fullRuleActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs
      (hforall
        (Index := ExactVisibleRule Z k)
        (Block := ExactVisiblePostSwitchSurface Z k)
        (fullRuleActualSwitchedLocalInterface Z k))

end FullRuleCounterexample

end Mettapedia.Computability.PNP
