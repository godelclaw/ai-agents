import Mettapedia.Computability.PNP.SharedExactABERMRoute

/-!
# P vs NP grassroots: final ERM interface for the shared-basis raw exact `(a, b)` route

This file packages the last manuscript-facing ingredients in the shared-basis
raw exact `(a, b)` ERM form:

* one shared affine basis on the raw exact `(a, b)` bits,
* one labeled sample assignment,
* one proof that the switched family is exactly the ERM wrapper on those
  samples,
* and one bad-code agreement bound.

Once those are supplied, the shared-basis raw exact compression and recovery
consequences follow automatically.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedExactABERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = sharedExactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q

section

variable [Inhabited Z] [Fintype Z]

def SharedExactABERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    SharedABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineDecisionListERMTargetData
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineDecisionListERMCompressionTarget
    (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem SharedExactABERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactABERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactABAffineDecisionListERMRecoveryLowerBound
    (Z := Z) (r := r) (k := k) (Index := Index)
    μ features samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP
