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

/-- The same true switched-history premise packages the manuscript-facing
exact-visible wrapper exactly as a finite selected-index representative cover of
size `2^s`. -/
theorem switchedHistoryExactVisibleCompressionWrapper_iff_finiteIndexRepresentativeCover_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items ↔
      T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget_of_true_fieldedSwitching
      (T := T) (s := s) (hist := hist) (items := items) hfield,
    exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover]

/-- And the same true switched-history premise packages the manuscript-facing
exact-visible wrapper exactly as a finite quotient-code presentation of size
`2^s`. -/
theorem switchedHistoryExactVisibleCompressionWrapper_iff_finitePredictorQuotient_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items ↔
      T.predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_exactVisibleCompressionTarget_of_true_fieldedSwitching
      (T := T) (s := s) (hist := hist) (items := items) hfield,
    exactVisibleCompressionTarget_iff_finitePredictorQuotient]

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

/-- So under a true fielded switching instance, the manuscript-facing clocked
wrapper is also exactly a finite selected-index representative cover of size
`2^s`. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finiteIndexRepresentativeCover_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items ↔
      T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield,
    IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover]

/-- And the same clocked wrapper is equally exactly a finite quotient-code
presentation of size `2^s`. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorQuotient_of_true_fieldedSwitching
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items ↔
      T.predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield,
    IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient]

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

/-- Failure of the representative-cover formulation already rules out the
exact-visible switched-history wrapper for that same concrete manuscript
history. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_not_finiteIndexRepresentativeCover
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ s)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_finiteIndexRepresentativeCover_of_true_fieldedSwitching
      (T := T) (s := s) (hist := hist) (items := items) hfield]
  exact hnot

/-- Failure of the quotient-code formulation already rules out the exact-visible
switched-history wrapper for that same concrete manuscript history. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_not_finitePredictorQuotient
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FinitePredictorQuotient (2 ^ s)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  rw [switchedHistoryExactVisibleCompressionWrapper_iff_finitePredictorQuotient_of_true_fieldedSwitching
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

/-- Failure of the representative-cover formulation already rules out the
clocked switched-history wrapper for that same concrete manuscript history. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_not_finiteIndexRepresentativeCover
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ s)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finiteIndexRepresentativeCover_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield]
  exact hnot

/-- Failure of the quotient-code formulation already rules out the clocked
switched-history wrapper for that same concrete manuscript history. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_not_finitePredictorQuotient
    {Ω : Type x} [Fintype Ω] [Fintype Z]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hnot : ¬ T.predictorFamily.FinitePredictorQuotient (2 ^ s)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  rw [switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorQuotient_of_true_fieldedSwitching
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield]
  exact hnot

/-- Under a true fielded switching instance, any manuscript-facing
exact-visible switched-history wrapper for a surjective actual family already
forces the full Boolean exact-visible classifier-space cardinality to fit
inside the advertised `2^s` budget. -/
theorem switchedHistoryExactVisibleCompressionWrapper_card_le_of_true_fieldedSwitching_of_surjective_predict
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ s := by
  exact
    exactVisible_finitePredictorCover_card_le_of_surjective_predict
      (Index := Index) hsurj
      ((switchedHistoryExactVisibleCompressionWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
        (T := T) (s := s) (hist := hist) (items := items) hfield).1 hwrap)

/-- The same explicit cardinal lower bound follows from the clocked
switched-history wrapper, since it is only another packaging of the same
finite-image burden. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_card_le_of_true_fieldedSwitching_of_surjective_predict
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ s := by
  exact
    exactVisible_finitePredictorCover_card_le_of_surjective_predict
      (Index := Index) hsurj
      ((switchedHistoryClockedKpolyFiniteLearningWrapper_iff_finitePredictorCover_of_true_fieldedSwitching
        (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield).1 hwrap)

/-- Equivalently, the exact-visible switched-history wrapper can only hold when
the visible post-switch surface itself has cardinality at most `s`. -/
theorem switchedHistoryExactVisibleCompressionWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  exact
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1
      (switchedHistoryExactVisibleCompressionWrapper_card_le_of_true_fieldedSwitching_of_surjective_predict
        (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hwrap)

/-- The clocked switched-history wrapper carries the same direct surface-width
burden, since it is only a repackaging of the same finite-image theorem. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  exact
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1
      (switchedHistoryClockedKpolyFiniteLearningWrapper_card_le_of_true_fieldedSwitching_of_surjective_predict
        (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hwrap)

/-- So if the visible post-switch surface is already larger than `s`, the
exact-visible switched-history wrapper is impossible for that concrete
manuscript history. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_s_lt_surfaceCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hcard : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  intro hwrap
  exact
    Nat.not_le_of_lt hcard
      (switchedHistoryExactVisibleCompressionWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
        (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hwrap)

/-- The same direct contradiction rules out the clocked switched-history
wrapper whenever the visible post-switch surface is larger than `s`. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_s_lt_surfaceCard
    [Fintype Z]
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface Z k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hcard : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  intro hwrap
  exact
    Nat.not_le_of_lt hcard
      (switchedHistoryClockedKpolyFiniteLearningWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
        (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hwrap)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
