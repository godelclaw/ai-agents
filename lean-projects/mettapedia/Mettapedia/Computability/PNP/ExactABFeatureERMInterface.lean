import Mettapedia.Computability.PNP.ExactABFeatureERMRoute

/-!
# P vs NP grassroots: final ERM interface for exact raw `(a, b)` features

This file packages the manuscript-facing ERM data for the non-shared exact
`(a, b)` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactABAffineFeatureERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples
  agreement_le :
    ∀ i,
      ∀ c : (exactABAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABAffineFeatureBitFamily Z r k).decode c.1) ≤ q

structure ExactABSparseThresholdERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (exactABSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactABAffineFeatureERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineFeatureERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABAffineFeatureERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 1) + 2 ^ r) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineFeatureERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABAffineFeatureERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 1) + 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABAffineFeatureERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 1) + 2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineFeatureBitFamily Z r k).bitExactRecoverySampleMass μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABAffineFeatureERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ samples q agreement_le i m

def ExactABSparseThresholdERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABSparseThresholdAffineERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABSparseThresholdERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 3)) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABSparseThresholdAffineERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) samples

theorem ExactABSparseThresholdERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 3) := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABSparseThresholdERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactABSparseThresholdAffineBitFamily Z r k).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactABSparseThresholdAffineERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
