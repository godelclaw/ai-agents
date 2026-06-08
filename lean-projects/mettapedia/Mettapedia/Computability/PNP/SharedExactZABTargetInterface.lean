import Mettapedia.Computability.PNP.SharedExactZABFeatureFamilies
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# P vs NP grassroots: target interfaces for the shared-basis `(zfeat(z), a, b)` route

This file packages the shared-basis route on the full manuscript-facing local
bits `(zfeat(z), a, b)`.

Once one fixed shared extractor and one fixed affine basis are supplied, the
remaining burden is just the choice of downstream combiner family.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABSparseThresholdTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

structure SharedExactZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G

section

theorem SharedExactZABAffineFeatureTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineFeatureFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABAffineFeatureTargetData.finitePredictorCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorCover (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.finiteIndexRepresentativeCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FiniteIndexRepresentativeCover (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.finitePredictorQuotient
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorQuotient (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) hsurj
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedExactZABSparseThresholdTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * p) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABSparseThresholdAffineFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABSparseThresholdTargetData.finitePredictorCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorCover (2 ^ (2 * p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 * p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABSparseThresholdTargetData.finiteIndexRepresentativeCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FiniteIndexRepresentativeCover (2 ^ (2 * p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := 2 * p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABSparseThresholdTargetData.finitePredictorQuotient
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorQuotient (2 ^ (2 * p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := 2 * p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABSparseThresholdTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * p := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 * p) (Index := Index) hsurj
      h.compressionTarget

theorem SharedExactZABSparseThresholdTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hs : 2 * p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedExactZABDecisionListTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineDecisionListFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABDecisionListTargetData.finitePredictorCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorCover (2 ^ (p + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := p + 1) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABDecisionListTargetData.finiteIndexRepresentativeCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FiniteIndexRepresentativeCover (2 ^ (p + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := p + 1) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABDecisionListTargetData.finitePredictorQuotient
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorQuotient (2 ^ (p + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := p + 1) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := p + 1) (Index := Index) hsurj
      h.compressionTarget

theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hs : p + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

structure SharedExactZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q

section

variable [Fintype Z]

theorem SharedExactZABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABDecisionListRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FinitePredictorCover (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorCover

theorem SharedExactZABDecisionListRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (p + 1)) := by
  exact (h.targetData).finiteIndexRepresentativeCover

theorem SharedExactZABDecisionListRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FinitePredictorQuotient (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorQuotient

theorem SharedExactZABDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hs : p + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact sharedExactZABAffineDecisionListRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat features
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
