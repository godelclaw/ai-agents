import Mettapedia.Computability.PNP.SharedExactZABERMRoute

/-!
# P vs NP grassroots: final ERM interface for the shared-basis exact `(zfeat(z), a, b)` route

This file packages the last manuscript-facing ingredients in the shared-basis
exact `z+a+b` ERM form:

* one shared extractor `zfeat`,
* one shared affine basis on the visible bits `(zfeat(z), a, b)`,
* one labeled sample assignment,
* one proof that the switched family is exactly the ERM wrapper on those
  samples,
* and one bad-code agreement bound.

Once those are supplied, the shared-basis exact compression and recovery
consequences follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABERMRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin p → AffineColumnCode (r + (k + k))
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = sharedExactZABAffineDecisionListERMFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q

section

variable [Fintype Z]

theorem SharedExactZABERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineDecisionListERMTargetData
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineDecisionListERMCompressionTarget
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABERMRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorCover

theorem SharedExactZABERMRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (p + 1)) := by
  exact (h.targetData).finiteIndexRepresentativeCover

theorem SharedExactZABERMRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorQuotient

theorem SharedExactZABERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : p + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineDecisionListERMRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    μ zfeat features samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
