import Mettapedia.Computability.PNP.SharedABFeatureRoutes
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction

/-!
# P vs NP grassroots: unified target interfaces for the shared raw `(a, b)` route

This file packages the current route bottleneck in one explicit interface style.

The mathematical burden is now cleanly separated:

* quotient invariance under the reduced raw visible surface `(a, b)`,
* one fixed shared affine basis on that reduced surface,
* one combiner class on the resulting shared feature vector.

Once those hypotheses are packaged, the exact-surface compression target follows
immediately with the corresponding budget.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- Target data for the shared raw `(a, b)` affine-feature route. -/
structure SharedABAffineFeatureTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` sparse-threshold route. -/
structure SharedABSparseThresholdTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` decision-list route. -/
structure SharedABDecisionListTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

section

variable [Inhabited Z]

theorem SharedABAffineFeatureTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 ^ r) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedABSparseThresholdTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABSparseThresholdTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 * r) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABSparseThresholdTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedABDecisionListTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r + 1) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

structure SharedABDecisionListRecoveryData
    [Inhabited Z]
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞)
    where
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

def SharedABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    SharedABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G where
  features := features
  invariant := h.invariant
  realized := h.realized

theorem SharedABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact (h.targetData).compressionTarget

theorem SharedABDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  have hexact :
      RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G :=
    realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k)
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) h.invariant)
      h.realized
  rcases hexact i with ⟨code, hcode⟩
  exact sharedExactABAffineDecisionListRecoveryLowerBound
    (Z := Z) (r := r) (k := k) features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
