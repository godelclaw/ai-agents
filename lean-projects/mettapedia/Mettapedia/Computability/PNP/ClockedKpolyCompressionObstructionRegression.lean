import Mettapedia.Computability.PNP.ClockedKpolyCompressionObstruction

/-!
# Regression checks for the clocked `Kpoly` compression obstruction

These wrappers pin the direct obstruction against handwaving the remaining
clocked `Kpoly` bridge: if the switched family is still fully expressive on the
exact visible post-switch surface, then no low-bit clocked realization family
can exist for it.
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyCompressionObstructionRegression

open Mettapedia.Computability.PNP

universe u v

theorem indexed_hasBitBudget_of_realizedByClockedBitFamily_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    {F : ClockedBitCodeFamily Input s clock}
    (hreal : G.RealizedByClockedBitFamily F) :
    G.HasBitBudget s := by
  exact IndexedPredictorFamily.hasBitBudget_of_realizedByClockedBitFamily hreal

theorem indexed_clockedBitBudget_lowerBound_of_surjective_predict_fintype_regression
    {Index : Type u} {Input : Type v} [Fintype Input]
    {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    {F : ClockedBitCodeFamily Input s clock}
    (hsurj : Function.Surjective G.predict)
    (hreal : G.RealizedByClockedBitFamily F) :
    Fintype.card Input ≤ s := by
  exact
    IndexedPredictorFamily.clockedBitBudget_lowerBound_of_surjective_predict_fintype
      (G := G) (s := s) (clock := clock) (F := F) hsurj hreal

theorem exactVisible_not_exists_clockedRealization_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_surjective_predict
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hs hsurj

theorem exactVisible_not_exists_clockedRealization_of_surjective_predict_of_lt_cardFormula_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card Z * 2 ^ k * 2 ^ k)
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hs hsurj

end Mettapedia.Computability.PNP.ClockedKpolyCompressionObstructionRegression
