import Mettapedia.Computability.PNP.ExactZABAffineFamilies
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction

/-!
# P vs NP grassroots: target interfaces for exact `(zfeat(z), a, b)` affine families

This file packages the non-shared exact `(zfeat(z), a, b)` affine-family routes
proved in the exact visible affine-family layer.

Unlike the shared-basis exact `z+a+b` route, these interfaces keep the full
non-shared code budgets of the underlying affine-feature, sparse-threshold, and
affine-decision-list classes explicit.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure ExactZABAffineFeatureTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactZABAffineFeatureFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G

structure ExactZABSparseThresholdTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactZABSparseThresholdAffineFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G

structure ExactZABAffineDecisionListTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByExactZABAffineDecisionListFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G

section

theorem ExactZABAffineFeatureTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 1) + 2 ^ p) := by
  exact exactVisibleCompressionTarget_of_realizedByExactZABAffineFeatureFamily
    (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem ExactZABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := p * ((r + (k + k)) + 1) + 2 ^ p) (Index := Index) hsurj
      h.compressionTarget

theorem ExactZABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hs : p * ((r + (k + k)) + 1) + 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem ExactZABSparseThresholdTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 3)) := by
  exact exactVisibleCompressionTarget_of_realizedByExactZABSparseThresholdAffineFamily
    (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem ExactZABSparseThresholdTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 3) := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := p * ((r + (k + k)) + 3)) (Index := Index) hsurj
      h.compressionTarget

theorem ExactZABSparseThresholdTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hs : p * ((r + (k + k)) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem ExactZABAffineDecisionListTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 2) + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByExactZABAffineDecisionListFamily
    (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem ExactZABAffineDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 2) + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := p * ((r + (k + k)) + 2) + 1) (Index := Index) hsurj
      h.compressionTarget

theorem ExactZABAffineDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hs : p * ((r + (k + k)) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

structure ExactZABAffineFeatureRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactZABAffineFeatureFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G
  agreement_le :
    ∀ i,
      ∀ c :
        (exactZABAffineFeatureBitFamily Z p r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((exactZABAffineFeatureBitFamily Z p r k zfeat).decode c.1) ≤ q

structure ExactZABSparseThresholdRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactZABSparseThresholdAffineFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G
  agreement_le :
    ∀ i,
      ∀ c :
        (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode c.1) ≤ q

structure ExactZABAffineDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByExactZABAffineDecisionListFamily
      (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G
  agreement_le :
    ∀ i,
      ∀ c :
        (exactZABAffineDecisionListBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((exactZABAffineDecisionListBitFamily Z p r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

def ExactZABAffineFeatureRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G := by
  exact ⟨h.realized⟩

theorem ExactZABAffineFeatureRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 1) + 2 ^ p) := by
  exact (h.targetData).compressionTarget

theorem ExactZABAffineFeatureRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineFeatureRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p * ((r + (k + k)) + 1) + 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABAffineFeatureRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 1) + 2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineFeatureBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact exactZABAffineFeatureRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

def ExactZABSparseThresholdRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G := by
  exact ⟨h.realized⟩

theorem ExactZABSparseThresholdRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 3)) := by
  exact (h.targetData).compressionTarget

theorem ExactZABSparseThresholdRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 3) := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABSparseThresholdRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p * ((r + (k + k)) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABSparseThresholdRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact exactZABSparseThresholdAffineRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

def ExactZABAffineDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABAffineDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G := by
  exact ⟨h.realized⟩

theorem ExactZABAffineDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 2) + 1) := by
  exact (h.targetData).compressionTarget

theorem ExactZABAffineDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 2) + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p * ((r + (k + k)) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABAffineDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineDecisionListBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact exactZABAffineDecisionListRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat
    (μ := μ) (target := G.predict i) (m := m)
    (h.realized i) (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
