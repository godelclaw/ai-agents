import Mettapedia.Computability.PNP.SharedExactZABTargetInterface

/-!
# P vs NP grassroots: recovery interfaces for the shared-basis exact `(zfeat(z), a, b)` route

This file packages the remaining generic ingredients for the shared-basis exact
`z+a+b` affine-feature and sparse-threshold routes:

* one shared extractor `zfeat`,
* one shared affine basis on the visible bits `(zfeat(z), a, b)`,
* one corresponding realization of the switched family through that basis, and
* one bad-code agreement bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABAffineFeatureRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  realized :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q

structure SharedExactZABSparseThresholdRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  realized :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q

section

variable [Fintype Z]

def SharedExactZABAffineFeatureRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABAffineFeatureRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABAffineFeatureRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABAffineFeatureRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h.realized i with ⟨code, hcode⟩
  exact sharedExactZABAffineFeatureRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

def SharedExactZABSparseThresholdRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABSparseThresholdRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * p) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABSparseThresholdRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABSparseThresholdRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : 2 * p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABSparseThresholdRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h.realized i with ⟨code, hcode⟩
  exact sharedExactZABSparseThresholdAffineRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
