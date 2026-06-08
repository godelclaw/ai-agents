import Mettapedia.Computability.PNP.SharedABTargetInterface

/-!
# P vs NP grassroots: recovery interfaces for the shared raw exact `(a, b)` route

This file packages the remaining generic ingredients for the shared raw exact
`(a, b)` affine-feature and sparse-threshold routes:

* one shared affine basis on the raw exact `(a, b)` bits,
* one corresponding realization of the switched family through that basis, and
* one bad-code agreement bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedABAffineFeatureRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q

structure SharedABSparseThresholdRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

def SharedABAffineFeatureRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABAffineFeatureTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G where
  features := h.features
  invariant := h.invariant
  realized := h.realized

theorem SharedABAffineFeatureRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact (h.targetData).compressionTarget

theorem SharedABAffineFeatureRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedABAffineFeatureRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedABAffineFeatureRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineFeatureBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  have hexact :
      RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k) h.features G :=
    realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k)
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant)
      h.realized
  rcases hexact i with ⟨code, hcode⟩
  exact sharedExactABAffineFeatureRecoveryLowerBound
    (Z := Z) (r := r) (k := k) h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

def SharedABSparseThresholdRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G where
  features := h.features
  invariant := h.invariant
  realized := h.realized

theorem SharedABSparseThresholdRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact (h.targetData).compressionTarget

theorem SharedABSparseThresholdRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedABSparseThresholdRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedABSparseThresholdRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  have hexact :
      RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) h.features G :=
    realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k)
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant)
      h.realized
  rcases hexact i with ⟨code, hcode⟩
  exact sharedExactABSparseThresholdAffineRecoveryLowerBound
    (Z := Z) (r := r) (k := k) h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
