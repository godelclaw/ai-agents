import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.CanonicalABRecoveryInterface

/-!
# P vs NP grassroots: ERM into the canonical raw `(a, b)` route

This file closes the same administrative gap for the raw exact `(a, b)` route
that the `z+a+b` side already handles.

Once the wrapper is honestly "ERM over this one raw `(a, b)` decision-list
class", the canonical code witness is not extra structure: it is exactly the
ERM-selected decision-list code at each index.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

/-- The canonical raw `(a, b)` decision-list code chosen by ERM for each
indexed sample. -/
noncomputable def canonicalABDecisionListERMCode
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    Index → SharedAffineDecisionListCode (k + k) :=
  fun i =>
    (sharedAffineDecisionListCodeEquivBitCode (k + k)).symm
      ((rawExactABDecisionListBitFamily Z k).empiricalRiskCode (samples i))

/-- The indexed exact-surface family obtained by running ERM inside the raw
`(a, b)` decision-list class. -/
noncomputable def canonicalABDecisionListERMFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (rawExactABDecisionListBitFamily Z k).indexedEmpiricalRiskFamily samples

theorem canonicalABDecisionListERMFamily_eq_canonicalABCodeFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    canonicalABDecisionListERMFamily (Z := Z) (k := k) samples =
      canonicalABCodeFamily
        (Z := Z) (k := k)
        (canonicalABDecisionListERMCode
          (Z := Z) (k := k) (Index := Index) samples) := by
  unfold canonicalABDecisionListERMFamily canonicalABCodeFamily
  congr

theorem canonicalABDecisionListERMCandidateData
    [Inhabited Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    CanonicalABDecisionListCandidateData
      (Z := Z) (k := k) (Index := Index)
      (canonicalABDecisionListERMFamily (Z := Z) (k := k) samples) := by
  exact candidateData_of_eq_canonicalABCodeFamily
    (Z := Z) (k := k) (Index := Index)
    (canonicalABDecisionListERMCode
      (Z := Z) (k := k) (Index := Index) samples)
    (canonicalABDecisionListERMFamily_eq_canonicalABCodeFamily
      (Z := Z) (k := k) (Index := Index) samples)

theorem canonicalABDecisionListERMCompressionTarget
    [Inhabited Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (canonicalABDecisionListERMFamily (Z := Z) (k := k) samples)
      (2 * k + 1) := by
  exact
    (canonicalABDecisionListERMCandidateData
      (Z := Z) (k := k) (Index := Index) samples).compressionTarget

theorem canonicalABDecisionListERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := Z) (k := k) samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * k + 1 := by
  exact
    (canonicalABDecisionListERMCandidateData
      (Z := Z) (k := k) (Index := Index) samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem canonicalABDecisionListERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := Z) (k := k) samples).predict := by
  exact
    (canonicalABDecisionListERMCandidateData
      (Z := Z) (k := k) (Index := Index) samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Inhabited Z] [Fintype Z]

noncomputable def canonicalABDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes
            ((canonicalABDecisionListERMFamily
              (Z := Z) (k := k) samples).predict i),
          agreementMass μ
            ((canonicalABDecisionListERMFamily
              (Z := Z) (k := k) samples).predict i)
            ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q) :
    CanonicalABDecisionListRecoveryData
      (Z := Z) (k := k) (Index := Index)
      μ
      (canonicalABDecisionListERMFamily (Z := Z) (k := k) samples) q := by
  refine ⟨
    canonicalABDecisionListERMCode
      (Z := Z) (k := k) (Index := Index) samples,
    canonicalABDecisionListERMFamily_eq_canonicalABCodeFamily
      (Z := Z) (k := k) (Index := Index) samples,
    hq
  ⟩

theorem canonicalABDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (rawExactABDecisionListBitFamily Z k).toEncodedFamily.BadCodes
            ((canonicalABDecisionListERMFamily
              (Z := Z) (k := k) samples).predict i),
          agreementMass μ
            ((canonicalABDecisionListERMFamily
              (Z := Z) (k := k) samples).predict i)
            ((rawExactABDecisionListBitFamily Z k).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactABDecisionListBitFamily Z k).bitExactRecoverySampleMass
        μ
        ((canonicalABDecisionListERMFamily
          (Z := Z) (k := k) samples).predict i)
        m := by
  exact
    (canonicalABDecisionListERMRecoveryData
      (Z := Z) (k := k) (Index := Index) μ samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
