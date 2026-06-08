import Mettapedia.Computability.PNP.ClockedKpolyBridge
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction

/-!
# P vs NP crux: clocked `Kpoly` realization still needs a real strict-subclass theorem

The remaining manuscript-side `Kpoly` burden is not merely to mention a
clocked decoder.  It is to realize the entire switched predictor family by a
clocked `s`-bit family on the exact visible post-switch surface.

This file records the corresponding obstruction directly.  If the switched
family on that exact surface is still rich enough to realize every Boolean rule
there, then no clocked `s`-bit realization family can exist below the full
surface-cardinality threshold.  So any successful `Kpoly` bridge must prove a
genuine strict-subclass theorem for the actual switched predictors.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v} {s clock : ℕ}

/-- If a finite visible family already realizes every Boolean rule on its input
surface, then any clocked realization family for it must use at least the full
surface cardinality many program bits. -/
theorem clockedBitBudget_lowerBound_of_surjective_predict_fintype
    [Fintype Input] {G : IndexedPredictorFamily Index Input}
    {F : ClockedBitCodeFamily Input s clock}
    (hsurj : Function.Surjective G.predict)
    (hreal : G.RealizedByClockedBitFamily F) :
    Fintype.card Input ≤ s := by
  classical
  exact
    bitBudget_lowerBound_of_surjective_predict_fintype
      (G := G) (s := s) hsurj
      (hasBitBudget_of_realizedByClockedBitFamily hreal)

/-- Hence, below the visible-surface cardinality threshold, no clocked `s`-bit
realization family can exist for a family already surjective onto the full
Boolean rule class on that surface. -/
theorem not_exists_clockedBitFamily_of_surjective_predict_fintype
    [Fintype Input] {G : IndexedPredictorFamily Index Input}
    (hs : s < Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F := by
  intro hclocked
  rcases hclocked with ⟨F, hreal⟩
  exact Nat.not_le_of_lt hs <|
    clockedBitBudget_lowerBound_of_surjective_predict_fintype
      (G := G) (s := s) (clock := clock) (F := F) hsurj hreal

end IndexedPredictorFamily

section ExactVisible

variable {Z : Type*} {k s clock : ℕ} {Index : Type*}

/-- If the exact switched family is still surjective onto the full Boolean rule
space on the manuscript-visible post-switch surface, then any clocked
realization family for it must use at least the full surface cardinality many
program bits. -/
theorem exactVisible_surfaceCard_le_of_clockedRealization_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hclocked :
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  classical
  rcases hclocked with ⟨F, hreal⟩
  exact
    IndexedPredictorFamily.clockedBitBudget_lowerBound_of_surjective_predict_fintype
      (G := G) (s := s) (clock := clock) (F := F) hsurj hreal

/-- Below the exact visible surface-cardinality threshold, no clocked
realization family can cover a switched family that is still surjective onto
the full Boolean rule space there. -/
theorem not_exists_clockedExactVisibleRealization_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    IndexedPredictorFamily.not_exists_clockedBitFamily_of_surjective_predict_fintype
      (G := G) (s := s) (clock := clock) hs hsurj

/-- Formula form of the same obstruction on the exact visible post-switch
surface. -/
theorem not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_cardFormula
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card Z * 2 ^ k * 2 ^ k)
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_surjective_predict
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (by simpa [card_exactVisiblePostSwitchSurface (Z := Z) (k := k)] using hs)
      hsurj

end ExactVisible

end Mettapedia.Computability.PNP
