import Mettapedia.Computability.PNP.ExactZABFeatureERMRoute

/-!
# P vs NP grassroots: final ERM interface for exact `(zfeat(z), a, b)` features

This file packages the manuscript-facing ERM data for the non-shared exact
`(zfeat(z), a, b)` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure ExactZABAffineFeatureERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = exactZABAffineFeatureERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples
  agreement_le :
    ∀ i,
      ∀ c :
        (exactZABAffineFeatureBitFamily Z p r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactZABAffineFeatureBitFamily Z p r k zfeat).decode c.1) ≤ q

structure ExactZABSparseThresholdERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G =
      exactZABSparseThresholdAffineERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples
  agreement_le :
    ∀ i,
      ∀ c :
        (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactZABAffineFeatureERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABAffineFeatureERMTargetData
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABAffineFeatureERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 1) + 2 ^ p) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABAffineFeatureERMCompressionTarget
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABAffineFeatureERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p * ((r + (k + k)) + 1) + 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABAffineFeatureERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 1) + 2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineFeatureBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABAffineFeatureERMRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    μ zfeat samples q agreement_le i m

def ExactZABSparseThresholdERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABSparseThresholdAffineERMTargetData
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABSparseThresholdERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 3)) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABSparseThresholdAffineERMCompressionTarget
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples

theorem ExactZABSparseThresholdERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 3) := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABSparseThresholdERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p * ((r + (k + k)) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABSparseThresholdERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact exactZABSparseThresholdAffineERMRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    μ zfeat samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
