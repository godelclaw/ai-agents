import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction

/-!
# PNP route bridge: actual switched-history wrappers

The remaining manuscript-facing switching route is not a global schema saying
that every fielded switching proof yields compression.  It is a one-family
wrapper: for the actual switched predictor family selected by the manuscript,
one concrete switched history is supposed to imply either the exact-visible
compression target or the bundled clocked finite-learning payload.

This file packages that wrapper directly and proves the two sharp outcomes
already available in the library:

* positive: if the actual switched family is realized by the shared exact
  `(zfeat z, a, b)` decision-list class, then the wrapper is immediate;
* negative: if the actual switched family is still fully expressive below the
  visible threshold and the fielded switching premise is actually true, then
  the wrapper is impossible.
-/

namespace Mettapedia.Computability.PNP

universe x u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- Manuscript-facing exact-visible wrapper: from one concrete fielded
switching proof on one concrete switched history, derive the exact-visible
compression target for the actual switched predictor family. -/
def SwitchedHistoryExactVisibleCompressionWrapper
    (Ω : Type x) [Fintype Ω]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (s : ℕ) (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) :
    Prop :=
  V13FieldSwitchingInstantiatedFrom hist items →
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) T.predictorFamily s

/-- Manuscript-facing clocked wrapper: from one concrete fielded switching
proof on one concrete switched history, derive the bundled clocked finite-
learning payload for the actual switched predictor family. -/
def SwitchedHistoryClockedKpolyFiniteLearningWrapper
    (Ω : Type x) [Fintype Ω] [Fintype Z]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (s clock : ℕ) (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) :
    Prop :=
  V13FieldSwitchingInstantiatedFrom hist items →
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock

theorem switchedHistoryClockedKpolyFiniteLearningWrapper_iff_exactVisibleCompressionWrapper
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items ↔
      SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  constructor
  · intro hwrap hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := T.predictorFamily)).mp
        (hwrap hfield)
  · intro hwrap hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := T.predictorFamily)).mpr
        (hwrap hfield)

namespace ZABDecisionListData

variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {zfeat : Z → BitVec r}

/-- Once the actual switched family is identified with the shared exact
decision-list surface, the manuscript-facing exact-visible switched-history
wrapper is immediate: the conclusion no longer depends on the switched-history
premise. -/
theorem switchedHistoryExactVisibleCompressionWrapper
    (h : ZABDecisionListData T zfeat)
    {Ω : Type x} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    SwitchedHistoryExactVisibleCompressionWrapper
      Ω T (r + 2 * k + 1) hist items := by
  intro _hfield
  exact h.exactVisibleCompressionTarget

/-- The same exact decision-list identification closes the manuscript-facing
clocked switched-history wrapper. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper
    [Fintype Z]
    (h : ZABDecisionListData T zfeat)
    {Ω : Type x} [Fintype Ω]
    {clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper
      Ω T (r + 2 * k + 1) clock hist items := by
  intro _hfield
  exact h.clockedKpolyFiniteLearningPayload (clock := clock)

end ZABDecisionListData

/-- If the fielded switching premise is actually true and the actual switched
predictor family is still fully expressive below the exact-visible threshold,
the manuscript-facing exact-visible switched-history wrapper is impossible. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  intro hwrap
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index)
      (G := T.predictorFamily) hs hsurj)
      (hwrap hfield)

/-- If the fielded switching premise is actually true and the actual switched
predictor family is still fully expressive below the full Boolean predictor-
space threshold, the manuscript-facing clocked switched-history wrapper is
impossible. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  intro hwrap
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := T.predictorFamily) hs hsurj)
      (hwrap hfield)

/-- Therefore any true exact-visible switched-history wrapper below the
surface threshold forces the actual switched predictor family to miss some
Boolean rule on the exact visible surface. -/
theorem not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_lt_surfaceCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      (T := T) (hist := hist) (items := items) hfield hsurj hs hwrap

/-- Therefore any true clocked switched-history wrapper below the full Boolean
predictor-space threshold forces the actual switched predictor family to miss
some Boolean rule on the exact visible surface. -/
theorem not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_lt_predictorCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      (T := T) (hist := hist) (items := items) hfield hsurj hs hwrap

/-- Specialization of the blocker to the full exact-visible Boolean family
already permitted by the bare actual-locality interface. -/
theorem fullRuleActualSwitchedLocalInterface_not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_lt_surfaceCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper
        Ω (fullRuleActualSwitchedLocalInterface Z k) s hist items := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      (T := fullRuleActualSwitchedLocalInterface Z k)
      (hist := hist) (items := items)
      hfield (fullRuleActualSwitchedLocalInterface_surjective Z k) hs

/-- Clocked specialization of the same full-rule actual-local blocker. -/
theorem fullRuleActualSwitchedLocalInterface_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_lt_predictorCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Ω (fullRuleActualSwitchedLocalInterface Z k) s clock hist items := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      (T := fullRuleActualSwitchedLocalInterface Z k)
      (hist := hist) (items := items)
      hfield (fullRuleActualSwitchedLocalInterface_surjective Z k) hs

/-- Therefore bare actual locality cannot support a universal exact-visible
switched-history wrapper theorem below the exact-visible truth-table
threshold. -/
theorem actualSwitchedLocalInterface_not_forall_switchedHistoryExactVisibleCompressionWrapper_of_lt_surfaceCard
    [Fintype Z]
    {s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} {Block : Type v} {Ω : Type x} [Fintype Ω]
        (T : ActualSwitchedLocalInterface Z k Index Block)
        (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)),
        SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items) := by
  intro hall
  exact
    fullRuleActualSwitchedLocalInterface_not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_lt_surfaceCard
      (Z := Z) (k := k)
      (Ω := ULift.{x} Bool)
      (hist := ([] : List (FiniteEvent (ULift.{x} Bool))))
      (items := ([] : List (V13FieldedStep (ULift.{x} Bool))))
      (by trivial)
      hs
      (hall
        (Index := ExactVisibleRule Z k)
        (Block := ExactVisiblePostSwitchSurface Z k)
        (Ω := ULift.{x} Bool)
        (fullRuleActualSwitchedLocalInterface Z k)
        []
        [])

/-- Therefore bare actual locality cannot support a universal clocked
switched-history wrapper theorem below the full Boolean predictor-space
threshold. -/
theorem actualSwitchedLocalInterface_not_forall_switchedHistoryClockedKpolyFiniteLearningWrapper_of_lt_predictorCard
    [Fintype Z]
    {s clock : ℕ}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} {Block : Type v} {Ω : Type x} [Fintype Ω]
        (T : ActualSwitchedLocalInterface Z k Index Block)
        (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)),
        SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items) := by
  intro hall
  exact
    fullRuleActualSwitchedLocalInterface_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_lt_predictorCard
      (Z := Z) (k := k)
      (Ω := ULift.{x} Bool)
      (hist := ([] : List (FiniteEvent (ULift.{x} Bool))))
      (items := ([] : List (V13FieldedStep (ULift.{x} Bool))))
      (by trivial)
      hs
      (hall
        (Index := ExactVisibleRule Z k)
        (Block := ExactVisiblePostSwitchSurface Z k)
        (Ω := ULift.{x} Bool)
        (fullRuleActualSwitchedLocalInterface Z k)
        []
        [])

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
