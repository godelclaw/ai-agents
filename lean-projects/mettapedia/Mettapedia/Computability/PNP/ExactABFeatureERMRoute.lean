import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.ExactABTargetInterface

/-!
# P vs NP grassroots: ERM over exact raw `(a, b)` feature classes

This file applies the generic ERM wrapper to the non-shared exact `(a, b)`
affine-feature and sparse-threshold classes.

Since the local hypothesis class is already fixed, the ERM-selected code is the
route witness directly.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

noncomputable def exactABAffineFeatureERMFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (exactABAffineFeatureBitFamily Z r k).indexedEmpiricalRiskFamily samples

noncomputable def exactABSparseThresholdAffineERMFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (exactABSparseThresholdAffineBitFamily Z r k).indexedEmpiricalRiskFamily samples

theorem exactABAffineFeatureERMTargetData
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactABAffineFeatureTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples) := by
  refine ⟨?_⟩
  intro i
  let code : AffineFeatureCode r (k + k) :=
    (affineFeatureCodeEquivBitCode r (k + k)).symm
      ((exactABAffineFeatureBitFamily Z r k).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  have hcode :
      affineFeatureCodeEquivBitCode r (k + k) code =
        (exactABAffineFeatureBitFamily Z r k).empiricalRiskCode (samples i) := by
    simp [code]
  calc
    (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples).predict i u
      = (exactABAffineFeatureBitFamily Z r k).decode
          ((exactABAffineFeatureBitFamily Z r k).empiricalRiskCode (samples i)) u := by
            rfl
    _ = (exactABAffineFeatureBitFamily Z r k).decode
          (affineFeatureCodeEquivBitCode r (k + k) code) u := by
            rw [hcode]
    _ = affineFeaturePredict code (exactABVisibleData u) := by
            exact congrFun
              (exactABAffineFeatureBitFamily_decode_code
                (Z := Z) (r := r) (k := k) code) u

theorem exactABSparseThresholdAffineERMTargetData
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples) := by
  refine ⟨?_⟩
  intro i
  let code : SparseThresholdAffineCode r (k + k) :=
    (sparseThresholdAffineCodeEquivBitCode r (k + k)).symm
      ((exactABSparseThresholdAffineBitFamily Z r k).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  have hcode :
      sparseThresholdAffineCodeEquivBitCode r (k + k) code =
        (exactABSparseThresholdAffineBitFamily Z r k).empiricalRiskCode (samples i) := by
    simp [code]
  calc
    (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples).predict i u
      = (exactABSparseThresholdAffineBitFamily Z r k).decode
          ((exactABSparseThresholdAffineBitFamily Z r k).empiricalRiskCode (samples i)) u := by
            rfl
    _ = (exactABSparseThresholdAffineBitFamily Z r k).decode
          (sparseThresholdAffineCodeEquivBitCode r (k + k) code) u := by
            rw [hcode]
    _ = sparseThresholdAffinePredict code (exactABVisibleData u) := by
            exact congrFun
              (exactABSparseThresholdAffineBitFamily_decode_code
                (Z := Z) (r := r) (k := k) code) u

theorem exactABAffineFeatureERMCompressionTarget
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples)
      (r * ((k + k) + 1) + 2 ^ r) := by
  exact
    (exactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).compressionTarget

theorem exactABSparseThresholdAffineERMCompressionTarget
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples)
      (r * ((k + k) + 3)) := by
  exact
    (exactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).compressionTarget

theorem exactABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact
    (exactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem exactABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r * ((k + k) + 3) := by
  exact
    (exactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem exactABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : r * ((k + k) + 1) + 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples).predict := by
  exact
    (exactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).not_surjective_predict_of_lt_surfaceCard
      hs

theorem exactABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : r * ((k + k) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples).predict := by
  exact
    (exactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Fintype Z]

def exactABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABAffineFeatureBitFamily Z r k).decode c.1) ≤ q) :
    ExactABAffineFeatureRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (exactABAffineFeatureERMFamily (Z := Z) (r := r) (k := k) samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).realized

def exactABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q) :
    ExactABSparseThresholdRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (exactABSparseThresholdAffineERMFamily (Z := Z) (r := r) (k := k) samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) samples).realized

theorem exactABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABAffineFeatureBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABAffineFeatureBitFamily Z r k).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 1) + 2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (exactABAffineFeatureBitFamily Z r k).bitExactRecoverySampleMass
        μ
        ((exactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) samples).predict i)
        m := by
  simpa [exactABAffineFeatureERMRecoveryData] using
    (exactABAffineFeatureERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ samples q hq).recoveryLowerBound i m

theorem exactABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactABSparseThresholdAffineBitFamily Z r k).toEncodedFamily.BadCodes
            ((exactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i),
          agreementMass μ
            ((exactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) samples).predict i)
            ((exactABSparseThresholdAffineBitFamily Z r k).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r * ((k + k) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactABSparseThresholdAffineBitFamily Z r k).bitExactRecoverySampleMass
        μ
        ((exactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) samples).predict i)
        m := by
  simpa [exactABSparseThresholdAffineERMRecoveryData] using
    (exactABSparseThresholdAffineERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
