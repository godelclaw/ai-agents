import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.ExactABTargetInterface

/-!
# P vs NP grassroots: ERM over exact raw `(a, b)` affine decision lists

This file applies the generic ERM wrapper to the non-shared exact `(a, b)`
affine-decision-list class.

Once the local hypothesis class is fixed, the ERM-selected code is the route
witness directly.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

noncomputable def exactABAffineDecisionListERMFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (exactABAffineDecisionListBitFamily Z r k).indexedEmpiricalRiskFamily samples

theorem exactABAffineDecisionListERMTargetData
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactABAffineDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples) := by
  refine ⟨?_⟩
  intro i
  let code : AffineDecisionListCode r (k + k) :=
    (affineDecisionListCodeEquivBitCode r (k + k)).symm
      ((exactABAffineDecisionListBitFamily Z r k).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  have hcode :
      affineDecisionListCodeEquivBitCode r (k + k) code =
        (exactABAffineDecisionListBitFamily Z r k).empiricalRiskCode (samples i) := by
    simp [code]
  calc
    (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples).predict i u
      = (exactABAffineDecisionListBitFamily Z r k).decode
          ((exactABAffineDecisionListBitFamily Z r k).empiricalRiskCode (samples i)) u := by
            rfl
    _ = (exactABAffineDecisionListBitFamily Z r k).decode
          (affineDecisionListCodeEquivBitCode r (k + k) code) u := by
            rw [hcode]
    _ = affineDecisionListPredict code (exactABVisibleData u) := by
            exact congrFun
              (exactABAffineDecisionListBitFamily_decode_code
                (Z := Z) (r := r) (k := k) code) u

theorem exactABAffineDecisionListERMCompressionTarget
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples)
      (r * ((k + k) + 2) + 1) := by
  exact
    (exactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).compressionTarget

theorem exactABAffineDecisionListERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 2) + 1 := by
  exact
    (exactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem exactABAffineDecisionListERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : r * ((k + k) + 2) + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples).predict := by
  exact
    (exactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Fintype Z]

def exactABAffineDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABAffineDecisionListBitFamily Z r k).decode c.1) ≤ q) :
    ExactABAffineDecisionListRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (exactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).realized

theorem exactABAffineDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABAffineDecisionListBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABAffineDecisionListBitFamily Z r k).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineDecisionListBitFamily Z r k).bitExactRecoverySampleMass
        μ
        ((exactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) samples).predict i)
        m := by
  simpa [exactABAffineDecisionListERMRecoveryData] using
    (exactABAffineDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
