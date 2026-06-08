import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure

/-!
# Regression checks for actual clocked `Kpoly` gap closure
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyActualGapClosureRegression

open scoped ENNReal
open Mettapedia.Computability.PNP

universe u v

theorem exact_zab_erm_payload_regression
    {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock := by
  exact
    exactZABDecisionListERMClockedKpolyFiniteLearningPayload
      (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
      zfeat samples

theorem bitvec_zab_erm_payload_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock := by
  exact
    bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
      (r := r) (k := k) (clock := clock) (Index := Index) samples

theorem equality_to_bitvec_erm_payload_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (clock := clock) (Index := Index) samples hG

theorem recovery_data_payload_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData
      (r := r) (k := k) (Index := Index) μ G q) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  exact h.clockedKpolyFiniteLearningPayload (clock := clock)

theorem full_family_not_finite_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (fullExactVisibleRuleFamily Z k).FinitePredictorCover (2 ^ s) := by
  exact
    fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem current_interface_not_forall_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP.ClockedKpolyActualGapClosureRegression
