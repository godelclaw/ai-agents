import Mettapedia.Computability.PNP.CanonicalABERMRoute

/-!
# P vs NP grassroots: final ERM interface for the canonical raw `(a, b)` route

This file packages the last manuscript-facing ingredients in the raw exact
`(a, b)` ERM form:

* one labeled sample assignment,
* one proof that the switched family is exactly the ERM wrapper on those
  samples,
* and one bad-code agreement bound.

Once those are supplied, the canonical raw exact compression and recovery
consequences follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

structure CanonicalABERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = canonicalABDecisionListERMFamily (Z := Z) (k := k) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

theorem CanonicalABERMRecoveryData.candidateData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := Z) (k := k) (Index := Index) μ G q) :
    CanonicalABDecisionListCandidateData
      (Z := Z) (k := k) (Index := Index) G := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalABDecisionListERMCandidateData
    (Z := Z) (k := k) (Index := Index) samples

theorem CanonicalABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := Z) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalABDecisionListERMCompressionTarget
    (Z := Z) (k := k) (Index := Index) samples

theorem CanonicalABERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := Z) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * k + 1 := by
  exact (h.candidateData).surfaceCard_le_of_surjective_predict hsurj

theorem CanonicalABERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := Z) (k := k) (Index := Index) μ G q)
    (hs : 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.candidateData).not_surjective_predict_of_lt_surfaceCard hs

theorem CanonicalABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := Z) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨samples, rfl, agreement_le⟩
  exact canonicalABDecisionListERMRecoveryLowerBound
    (Z := Z) (k := k) (Index := Index)
    μ samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
