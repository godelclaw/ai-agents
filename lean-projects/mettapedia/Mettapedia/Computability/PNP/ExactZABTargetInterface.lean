import Mettapedia.Computability.PNP.ExactZABDecisionListFamily
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# P vs NP grassroots: target interfaces for the shared `z+a+b` decision-list route

This file packages the new manuscript-shaped candidate route:

* one fixed shared extractor `zfeat : Z → BitVec r`,
* one fixed-order decision-list family on the exact visible bits `(zfeat z, a, b)`,
* and, when needed, one uniform bad-code agreement bound.

This keeps the remaining burden explicit: exhibit the actual switched family as
one such realized family, then control the bad-code agreement mass.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure ExactZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) where
  realized :
    RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G

section

theorem ExactZABDecisionListTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

theorem ExactZABDecisionListTargetData.compressionTarget_twoMul
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact exactVisibleCompressionTarget_of_realizedByRawExactZABDecisionListFamily_twoMul
    (Z := Z) (r := r) (k := k) (Index := Index) zfeat h.realized

/-- The direct exact `(zfeat(z), a, b)` decision-list route supplies the
finite predictor-image object required by the exact-visible `Kpoly` boundary. -/
theorem ExactZABDecisionListTargetData.finitePredictorCover_twoMul
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := r + 2 * k + 1) (Index := Index) (G := G)).mp
      h.compressionTarget_twoMul

/-- The same direct route supplies actual representative indices for the
finite predictor image. -/
theorem ExactZABDecisionListTargetData.finiteIndexRepresentativeCover_twoMul
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := r + 2 * k + 1) (Index := Index) (G := G)).mp
      h.compressionTarget_twoMul

/-- The same direct route supplies a quotient-code presentation of the finite
predictor image. -/
theorem ExactZABDecisionListTargetData.finitePredictorQuotient_twoMul
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := r + 2 * k + 1) (Index := Index) (G := G)).mp
      h.compressionTarget_twoMul

theorem ExactZABDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r + 2 * k + 1) (Index := Index) hsurj
      h.compressionTarget_twoMul

theorem ExactZABDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

structure ExactZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedByRawExactZABDecisionListFamily (Z := Z) (r := r) (k := k) zfeat G
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1) ≤ q

section

variable [Fintype Z]

theorem ExactZABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactZABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) zfeat G := by
  exact ⟨h.realized⟩

theorem ExactZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  exact (h.targetData).compressionTarget

theorem ExactZABDecisionListRecoveryData.compressionTarget_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.targetData).compressionTarget_twoMul

theorem ExactZABDecisionListRecoveryData.finitePredictorCover_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finitePredictorCover_twoMul

theorem ExactZABDecisionListRecoveryData.finiteIndexRepresentativeCover_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finiteIndexRepresentativeCover_twoMul

theorem ExactZABDecisionListRecoveryData.finitePredictorQuotient_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact (h.targetData).finitePredictorQuotient_twoMul

theorem ExactZABDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 2 * k + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem ExactZABDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem ExactZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + (k + k) + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact rawExactZABDecisionListRecoveryLowerBound
    (Z := Z) (r := r) (k := k) zfeat
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

theorem ExactZABDecisionListRecoveryData.recoveryLowerBound_twoMul
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).bitExactRecoverySampleMass μ (G.predict i) m := by
  exact rawExactZABDecisionListRecoveryLowerBound_twoMul
    (Z := Z) (r := r) (k := k) zfeat
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP
