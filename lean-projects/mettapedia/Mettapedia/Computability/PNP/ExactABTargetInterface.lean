import Mettapedia.Computability.PNP.ExactABAffineFamilies
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction

/-!
# P vs NP grassroots: target interfaces for exact raw `(a, b)` affine families

This file packages the non-shared exact `(a, b)` routes already proved in the
raw exact affine-family layer.

Unlike the shared-basis routes, these interfaces keep the full code budgets of
the underlying affine-feature, sparse-threshold, and affine-decision-list
classes explicit.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactABAffineFeatureTargetData
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactABAffineFeatureFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G

structure ExactABSparseThresholdTargetData
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactABSparseThresholdAffineFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G

structure ExactABAffineDecisionListTargetData
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactABAffineDecisionListFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G

section

theorem ExactABAffineFeatureTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 1) + 2 ^ r) := by
  exact exactVisibleCompressionTarget_of_realizedByExactABAffineFeatureFamily
    (r := r) (Z := Z) (k := k) (Index := Index) h.realized

theorem ExactABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r * ((k + k) + 1) + 2 ^ r) (Index := Index) hsurj
      h.compressionTarget

theorem ExactABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : r * ((k + k) + 1) + 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem ExactABSparseThresholdTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 3)) := by
  exact exactVisibleCompressionTarget_of_realizedByExactABSparseThresholdAffineFamily
    (r := r) (Z := Z) (k := k) (Index := Index) h.realized

theorem ExactABSparseThresholdTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 3) := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r * ((k + k) + 3)) (Index := Index) hsurj
      h.compressionTarget

theorem ExactABSparseThresholdTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : r * ((k + k) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem ExactABAffineDecisionListTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactABAffineDecisionListTargetData
        (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 2) + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByExactABAffineDecisionListFamily
    (r := r) (Z := Z) (k := k) (Index := Index) h.realized

theorem ExactABAffineDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactABAffineDecisionListTargetData
        (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 2) + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r * ((k + k) + 2) + 1) (Index := Index) hsurj
      h.compressionTarget

theorem ExactABAffineDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactABAffineDecisionListTargetData
        (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : r * ((k + k) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

structure ExactABAffineFeatureRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactABAffineFeatureFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G
  agreement_le :
    ∀ i,
      ∀ c : (exactABAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABAffineFeatureBitFamily Z r k).decode c.1) ≤ q

structure ExactABSparseThresholdRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactABSparseThresholdAffineFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G
  agreement_le :
    ∀ i,
      ∀ c :
        (exactABSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q

structure ExactABAffineDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactABAffineDecisionListFamily
      (r := r) (Z := Z) (k := k) (Index := Index) G
  agreement_le :
    ∀ i,
      ∀ c :
        (exactABAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactABAffineDecisionListBitFamily Z r k).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactABAffineFeatureRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G := by
  exact ⟨h.realized⟩

theorem ExactABAffineFeatureRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 1) + 2 ^ r) := by
  exact (h.targetData).compressionTarget

theorem ExactABAffineFeatureRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineFeatureRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 1) + 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABAffineFeatureRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 1) + 2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineFeatureBitFamily Z r k).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact exactABAffineFeatureRecoveryLowerBound
    (Z := Z) (r := r) (k := k)
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

def ExactABSparseThresholdRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G := by
  exact ⟨h.realized⟩

theorem ExactABSparseThresholdRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 3)) := by
  exact (h.targetData).compressionTarget

theorem ExactABSparseThresholdRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 3) := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABSparseThresholdRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABSparseThresholdRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactABSparseThresholdAffineBitFamily Z r k).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact exactABSparseThresholdAffineRecoveryLowerBound
    (Z := Z) (r := r) (k := k)
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

def ExactABAffineDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactABAffineDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G := by
  exact ⟨h.realized⟩

theorem ExactABAffineDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r * ((k + k) + 2) + 1) := by
  exact (h.targetData).compressionTarget

theorem ExactABAffineDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 2) + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r * ((k + k) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactABAffineDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineDecisionListBitFamily Z r k).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact exactABAffineDecisionListRecoveryLowerBound
    (Z := Z) (r := r) (k := k)
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
