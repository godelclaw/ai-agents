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
    not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_s_lt_surfaceCard
      (T := T) (s := r + 2 * k + 1) (hist := hist) (items := items)
      hfield hsurj
      (switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
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
    not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_s_lt_surfaceCard
      (T := T) (s := r + 2 * k + 1) (clock := clock) (hist := hist) (items := items)
      hfield hsurj
      (switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
        (n := n) (k := k) (r := r) hr hwidth)

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
    not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_lt_surfaceCard
      (T := T) (s := r + 2 * k + 1) (hist := hist) (items := items)
      hwrap hfield
      (switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
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
    not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_lt_predictorCard
      (T := T) (s := r + 2 * k + 1) (clock := clock) (hist := hist) (items := items)
      hwrap hfield
      (by
        simpa using
          (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2
            (switchedHistoryBudget_lt_surfaceCard_of_le_of_two_le
              (n := n) (k := k) (r := r) hr hwidth))

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
