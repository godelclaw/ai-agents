import Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalence

/-!
# Regression checks for the clocked `Kpoly` bridge equivalence

These wrappers pin the fact that the clocked realization interface is exactly
the existing exact bit-budget interface.  The clock is bookkeeping; the live
mathematical burden remains the small-class theorem for the actual switched
family.
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalenceRegression

open Mettapedia.Computability.PNP

universe u v

theorem indexed_constructed_clockedBitFamily_realizes_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (hbudget : G.HasBitBudget s) :
    G.RealizedByClockedBitFamily
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock hbudget) := by
  exact
    IndexedPredictorFamily.realizedByClockedBitFamily_clockedBitCodeFamilyOfHasBitBudget
      (G := G) (s := s) clock hbudget

theorem indexed_exists_clockedBitFamily_iff_hasBitBudget_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input} :
    (∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      G.HasBitBudget s := by
  exact IndexedPredictorFamily.exists_clockedBitFamily_iff_hasBitBudget
    (G := G) (s := s) (clock := clock)

theorem indexed_exists_clockedBitFamily_iff_exists_clockedBitFamily_of_clock_regression
    {Index : Type u} {Input : Type v} {s clock clock' : ℕ}
    {G : IndexedPredictorFamily Index Input} :
    (∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily Input s clock', G.RealizedByClockedBitFamily F := by
  exact IndexedPredictorFamily.exists_clockedBitFamily_iff_exists_clockedBitFamily_of_clock
    (G := G) (s := s) (clock := clock) (clock' := clock')

theorem indexed_not_exists_clockedBitFamily_iff_not_hasBitBudget_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input} :
    (¬ ∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      ¬ G.HasBitBudget s := by
  exact IndexedPredictorFamily.not_exists_clockedBitFamily_iff_not_hasBitBudget
    (G := G) (s := s) (clock := clock)

theorem exact_visible_exists_clockedRealization_iff_exactVisibleCompressionTarget_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)

theorem exact_visible_exists_clockedRealization_iff_of_clock_regression
    {Z : Type*} {k s clock clock' : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock',
        G.RealizedByClockedBitFamily F := by
  exact exists_clockedExactVisibleRealization_iff_of_clock
    (G := G) (s := s) (clock := clock) (clock' := clock')

theorem exact_visible_not_exists_clockedRealization_iff_not_exactVisibleCompressionTarget_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact not_exists_clockedExactVisibleRealization_iff_not_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)

theorem exact_visible_compressionTarget_of_exists_clockedRealization_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hclocked :
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact exactVisibleCompressionTarget_of_exists_clockedExactVisibleRealization
    (G := G) (s := s) (clock := clock) hclocked

theorem exact_visible_exists_clockedRealization_of_exactVisibleCompressionTarget_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
      G.RealizedByClockedBitFamily F := by
  exact exists_clockedExactVisibleRealization_of_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock) hsmall

theorem exact_visible_constructed_clockedFamily_realizes_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    G.RealizedByClockedBitFamily
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock hsmall) := by
  exact
    realizedByClockedExactVisibleFamily_of_exactVisibleCompressionTarget
      (G := G) (s := s) (clock := clock) hsmall

end Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalenceRegression
