import Mettapedia.Computability.PNP.ExactZABFeatureERMInterface
import Mettapedia.Computability.PNP.ExactZABERMRoute

/-!
# P vs NP grassroots: final ERM interface for exact `(zfeat(z), a, b)` routes

This file completes the manuscript-facing ERM interface for the non-shared
exact `(zfeat(z), a, b)` route by packaging the raw exact decision-list wrapper.

The affine-feature and sparse-threshold ERM interfaces are re-exported from
`ExactZABFeatureERMInterface`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactZABERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactZABDecisionListERMFamily (Z := Z) (r := r) (k := k) zfeat samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactZABERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABDecisionListERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABDecisionListERMCompressionTarget_twoMul
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABERMRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finitePredictorCover_twoMul

theorem ExactZABERMRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finiteIndexRepresentativeCover_twoMul

theorem ExactZABERMRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finitePredictorQuotient_twoMul

theorem ExactZABERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 2 * k + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABDecisionListERMRecoveryLowerBound_twoMul
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ zfeat samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
