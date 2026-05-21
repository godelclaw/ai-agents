import Mettapedia.Computability.PNP.ActualSwitchedHistoryRouteReduction
import Mettapedia.Computability.PNP.ExactZABCompressionObstruction

/-!
# PNP route obstruction: switched-history wrappers at manuscript bit budgets

On the concrete bit-valued latent surface `Z = BitVec n`, the manuscript-shaped
budget `r + 2*k + 1` is already smaller than the full exact visible
truth-table size whenever `r ≤ n` and the visible width `n + 2*k` is at least
`2`.

This file lifts that arithmetic directly to the switched-history wrapper route:
if a concrete fielded switching instance is true and the actual switched family
is still surjective, then neither the exact-visible nor the clocked wrapper can
hold at that budget.
-/

namespace Mettapedia.Computability.PNP

universe x u v

namespace ActualSwitchedLocalInterface

variable {n k r : ℕ} {Index : Type u} {Block : Type v}

/-- On the concrete bit-valued latent surface, any true exact-visible
switched-history wrapper for a surjective actual switched family already forces
the full truth-table lower bound `2^(n + 2*k) ≤ s`. -/
theorem switchedHistoryExactVisibleCompressionWrapper_bitVecSurfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items) :
    2 ^ (n + 2 * k) ≤ s := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    switchedHistoryExactVisibleCompressionWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hwrap

/-- The same full truth-table lower bound follows from the clocked
switched-history wrapper, since it is the same finite-image burden. -/
theorem switchedHistoryClockedKpolyFiniteLearningWrapper_bitVecSurfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items) :
    2 ^ (n + 2 * k) ≤ s := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    switchedHistoryClockedKpolyFiniteLearningWrapper_surfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hwrap

/-- Therefore any explicit budget gap below the full truth-table size already
rules out the exact-visible switched-history wrapper on the bit-valued latent
surface. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hbudget : s < 2 ^ (n + 2 * k)) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  intro hwrap
  exact Nat.not_le_of_lt hbudget <|
    switchedHistoryExactVisibleCompressionWrapper_bitVecSurfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hwrap

/-- The same explicit budget gap already rules out the clocked
switched-history wrapper on the bit-valued latent surface. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hbudget : s < 2 ^ (n + 2 * k)) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  intro hwrap
  exact Nat.not_le_of_lt hbudget <|
    switchedHistoryClockedKpolyFiniteLearningWrapper_bitVecSurfaceCard_le_of_true_fieldedSwitching_of_surjective_predict
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hwrap

/-- Equivalently, any exact-visible switched-history wrapper below the full
truth-table size already forces non-surjectivity of the actual switched family
on the bit-valued latent surface. -/
theorem not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_budget_lt
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hbudget : s < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hbudget hwrap

/-- And likewise for the clocked switched-history wrapper below the full
truth-table size. -/
theorem not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_budget_lt
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hbudget : s < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hbudget hwrap

/-- On the concrete bit-valued visible surface, the manuscript-shaped budget
`r + 2*k + 1` is strictly below the full exact visible surface cardinality as
soon as the extractor width does not exceed the latent width and the visible
surface is nontrivial. -/
theorem switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
  have hbudget :
      r + 2 * k + 1 < 2 ^ (n + 2 * k) :=
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
      (n := n) (r := r) (k := k) hr hwidth
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using hbudget

/-- Therefore a true switched-history exact-visible wrapper at the manuscript
budget is incompatible with surjectivity of the actual switched family on the
full bit-valued exact visible surface. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T (r + 2 * k + 1) hist items := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := r + 2 * k + 1) (hist := hist) (items := items)
      hfield hsurj
      (by
        simpa [card_exactVisiblePostSwitchSurface_bitVec] using
          switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
            (n := n) (k := k) (r := r) hr hwidth)

/-- The same route-level contradiction rules out the clocked switched-history
wrapper at the same manuscript budget. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T (r + 2 * k + 1) clock hist items := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := r + 2 * k + 1) (clock := clock) (hist := hist) (items := items)
      hfield hsurj
      (by
        simpa [card_exactVisiblePostSwitchSurface_bitVec] using
          switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
            (n := n) (k := k) (r := r) hr hwidth)

/-- In particular, the full-width manuscript budget `n + 2*k + 1` is already
ruled out for the exact-visible switched-history wrapper as soon as the raw
visible width is at least `2`. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_two_le_visibleWidth
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T (n + 2 * k + 1) hist items := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
      (T := T) (r := n) (hist := hist) (items := items) hfield hsurj (le_rfl) hwidth

/-- More generally, once the raw visible width is at least `2`, any
switched-history exact-visible wrapper whose budget stays at or below the
full-width linear threshold `n + 2*k + 1` is impossible. -/
theorem not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items := by
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj
      (lt_of_le_of_lt hs <|
        exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
          (r := n) (k := k) hwidth)

/-- The same direct full-width obstruction rules out the clocked
switched-history wrapper. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_two_le_visibleWidth
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T (n + 2 * k + 1) clock hist items := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_of_two_le
      (T := T) (r := n) (clock := clock) (hist := hist) (items := items) hfield hsurj (le_rfl) hwidth

/-- The same linear-threshold obstruction rules out every clocked
switched-history wrapper at budget at most `n + 2*k + 1`. -/
theorem not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items := by
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_budget_lt
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj
      (lt_of_le_of_lt hs <|
        exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
          (r := n) (k := k) hwidth)

/-- Equivalently, any true exact-visible switched-history wrapper at that
budget already forces the actual switched family to miss some Boolean rule on
the full bit-valued visible surface. -/
theorem not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_le_of_two_le
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T (r + 2 * k + 1) hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_budget_lt
      (T := T) (s := r + 2 * k + 1) (hist := hist) (items := items)
      hwrap hfield
      (by
        simpa [card_exactVisiblePostSwitchSurface_bitVec] using
          switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
            (n := n) (k := k) (r := r) hr hwidth)

/-- And likewise for the clocked switched-history wrapper at the same concrete
budget. -/
theorem not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_le_of_two_le
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T (r + 2 * k + 1) clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hr : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_budget_lt
      (T := T) (s := r + 2 * k + 1) (clock := clock) (hist := hist) (items := items)
      hwrap hfield
      (by
        simpa [card_exactVisiblePostSwitchSurface_bitVec] using
          switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
            (n := n) (k := k) (r := r) hr hwidth)

/-- Equivalently, the full-width exact-visible switched-history wrapper already
forces non-surjectivity once the raw visible width is at least `2`. -/
theorem not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_two_le_visibleWidth
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T (n + 2 * k + 1) hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_le_of_two_le
      (T := T) (r := n) (hist := hist) (items := items) hwrap hfield (le_rfl) hwidth

/-- Equivalently, any exact-visible switched-history wrapper at budget at most
`n + 2*k + 1` already forces non-surjectivity once the raw visible width is at
least `2`. -/
theorem not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hs hwidth hwrap

/-- And likewise for the full-width clocked switched-history wrapper. -/
theorem not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_two_le_visibleWidth
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T (n + 2 * k + 1) clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_le_of_two_le
      (T := T) (r := n) (clock := clock) (hist := hist) (items := items) hwrap hfield (le_rfl) hwidth

/-- And likewise for every clocked switched-history wrapper whose budget stays
at or below `n + 2*k + 1`. -/
theorem not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
    {Ω : Type x} [Fintype Ω]
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {s clock : ℕ} {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items) hfield hsurj hs hwidth hwrap

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
