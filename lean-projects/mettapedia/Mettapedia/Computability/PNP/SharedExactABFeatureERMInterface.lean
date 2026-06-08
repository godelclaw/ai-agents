import Mettapedia.Computability.PNP.SharedExactABFeatureERMRoute

/-!
# P vs NP grassroots: final ERM interface for shared raw exact `(a, b)` features

This file packages the last manuscript-facing ingredients for ERM over the
shared raw exact `(a, b)` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedExactABAffineFeatureERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = sharedExactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q

structure SharedExactABSparseThresholdERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G =
      sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

def SharedExactABAffineFeatureERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABAffineFeatureTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineFeatureERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABAffineFeatureERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineFeatureERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABAffineFeatureERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactABAffineFeatureERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineFeatureBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineFeatureERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ features samples q agreement_le i m

def SharedExactABSparseThresholdERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABSparseThresholdERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABSparseThresholdERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactABSparseThresholdERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABSparseThresholdAffineERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ features samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
