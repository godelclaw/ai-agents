import Mettapedia.Computability.PNP.ExactABFeatureERMInterface
import Mettapedia.Computability.PNP.ExactABERMRoute

/-!
# P vs NP grassroots: final ERM interface for exact raw `(a, b)` routes

This file completes the manuscript-facing ERM interface for the non-shared
exact `(a, b)` route by packaging the affine-decision-list wrapper.

The affine-feature and sparse-threshold ERM interfaces are re-exported from
`ExactABFeatureERMInterface`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactABAffineDecisionListERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (exactABAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABAffineDecisionListBitFamily Z r k).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactABAffineDecisionListERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABAffineDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineDecisionListERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABAffineDecisionListERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 2) + 1) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineDecisionListERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABAffineDecisionListERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 2) + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineDecisionListERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABAffineDecisionListERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineDecisionListBitFamily Z r k).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineDecisionListERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
