import Mettapedia.Computability.PNP.ActualSwitchedHistoryWrapper

/-!
# PNP route reduction: actual switched-history wrappers

Once a concrete manuscript switched-history instance is fixed and its fielded
switching premise is actually true, the remaining wrapper obligation is not a
new kind of bridge theorem. It is exactly the existing finite-image burden for
the actual switched predictor family.
-/

namespace Mettapedia.Computability.PNP

universe x u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- Under a true fielded switching instance, the manuscript-facing exact-visible
switched-history wrapper is exactly the usual exact-visible compression target
for the actual switched family. -/
theorem switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := Index) T.predictorFamily s := by
  constructor
  · intro hwrap
    exact hwrap hfield
  · intro htarget _hfield
    exact htarget

/-- Under a true fielded switching instance, the manuscript-facing clocked
switched-history wrapper is exactly the usual clocked finite-learning payload
for the actual switched family. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_iff_clockedKpolyFiniteLearningPayload_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items ↔
      ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  constructor
  · intro hwrap
    exact hwrap hfield
  · intro hpayload _hfield
    exact hpayload

/-- Therefore, under a true fielded switching instance, the manuscript-facing
exact-visible wrapper is exactly a finite predictor-image cover of size
`2^s`. -/
theorem switchedHistoryExactVisibleCompressionWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items ↔
      T.predictorFamily.FinitePredictorCover (2 ^ s) := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget_of_true_fieldedSwitching
      (T := T) (s := s) (hist := hist) (items := items) hfield,
    exactVisibleCompressionTarget_iff_finitePredictorCover]

/-- Likewise, under a true fielded switching instance, the manuscript-facing
clocked wrapper is exactly the same finite predictor-image cover obligation. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items ↔
      T.predictorFamily.FinitePredictorCover (2 ^ s) := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_clockedKpolyFiniteLearningPayload_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield,
    clockedKpolyFiniteLearningPayload_iff_finitePredictorCover]

/-- So failure of the finite predictor-cover theorem already rules out the
exact-visible switched-history wrapper for that concrete manuscript history. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_not_finitePredictorCover
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FinitePredictorCover (2 ^ s)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
      (T := T) (s := s) (hist := hist) (items := items) hfield]
  exact hnot

/-- And failure of the same finite predictor-cover theorem already rules out the
clocked switched-history wrapper for that concrete manuscript history. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_not_finitePredictorCover
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FinitePredictorCover (2 ^ s)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield]
  exact hnot

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
