import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.ExactZABAffineTargetInterface

/-!
# P vs NP grassroots: ERM over exact `(zfeat(z), a, b)` feature classes

This file applies the generic ERM wrapper to the non-shared exact
`(zfeat(z), a, b)` affine-feature and sparse-threshold classes.

Since the local hypothesis class is already fixed, the ERM-selected code is the
route witness directly.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

noncomputable def exactZABAffineFeatureERMFamily
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (exactZABAffineFeatureBitFamily Z p r k zfeat).indexedEmpiricalRiskFamily samples

noncomputable def exactZABSparseThresholdAffineERMFamily
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).indexedEmpiricalRiskFamily samples

theorem exactZABAffineFeatureERMTargetData
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat
      (exactZABAffineFeatureERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples) := by
  refine ⟨?_⟩
  intro i
  let code : AffineFeatureCode p (r + (k + k)) :=
    (affineFeatureCodeEquivBitCode p (r + (k + k))).symm
      ((exactZABAffineFeatureBitFamily Z p r k zfeat).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  have hcode :
      affineFeatureCodeEquivBitCode p (r + (k + k)) code =
        (exactZABAffineFeatureBitFamily Z p r k zfeat).empiricalRiskCode (samples i) := by
    simp [code]
  calc
    (exactZABAffineFeatureERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i u
      = (exactZABAffineFeatureBitFamily Z p r k zfeat).decode
          ((exactZABAffineFeatureBitFamily Z p r k zfeat).empiricalRiskCode (samples i)) u := by
            rfl
    _ = (exactZABAffineFeatureBitFamily Z p r k zfeat).decode
          (affineFeatureCodeEquivBitCode p (r + (k + k)) code) u := by
            rw [hcode]
    _ = affineFeaturePredict code
          (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
            exact congrFun
              (exactZABAffineFeatureBitFamily_decode_code
                (Z := Z) (p := p) (r := r) (k := k) zfeat code) u

theorem exactZABSparseThresholdAffineERMTargetData
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat
      (exactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat samples) := by
  refine ⟨?_⟩
  intro i
  let code : SparseThresholdAffineCode p (r + (k + k)) :=
    (sparseThresholdAffineCodeEquivBitCode p (r + (k + k))).symm
      ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  have hcode :
      sparseThresholdAffineCodeEquivBitCode p (r + (k + k)) code =
        (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).empiricalRiskCode (samples i) := by
    simp [code]
  calc
    (exactZABSparseThresholdAffineERMFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i u
      = (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode
          ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).empiricalRiskCode (samples i)) u := by
            rfl
    _ = (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode
          (sparseThresholdAffineCodeEquivBitCode p (r + (k + k)) code) u := by
            rw [hcode]
    _ = sparseThresholdAffinePredict code
          (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
            exact congrFun
              (exactZABSparseThresholdAffineBitFamily_decode_code
                (Z := Z) (p := p) (r := r) (k := k) zfeat code) u

theorem exactZABAffineFeatureERMCompressionTarget
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactZABAffineFeatureERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples)
      (p * ((r + (k + k)) + 1) + 2 ^ p) := by
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).compressionTarget

theorem exactZABSparseThresholdAffineERMCompressionTarget
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (exactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat samples)
      (p * ((r + (k + k)) + 3)) := by
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).compressionTarget

theorem exactZABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem exactZABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p * ((r + (k + k)) + 3) := by
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem exactZABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : p * ((r + (k + k)) + 1) + 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_lt_surfaceCard
      hs

theorem exactZABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : p * ((r + (k + k)) + 3) < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Fintype Z]

def exactZABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactZABAffineFeatureBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
            ((exactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
            ((exactZABAffineFeatureBitFamily Z p r k zfeat).decode c.1) ≤ q) :
    ExactZABAffineFeatureRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (exactZABAffineFeatureERMFamily (Z := Z) (p := p) (r := r) (k := k) zfeat samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).realized

def exactZABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
            ((exactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
            ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode c.1) ≤ q) :
    ExactZABSparseThresholdRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (exactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat samples) q := by
  refine ⟨?_, hq⟩
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).realized

theorem exactZABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactZABAffineFeatureBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
            ((exactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
            ((exactZABAffineFeatureBitFamily Z p r k zfeat).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 1) + 2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineFeatureBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ
        ((exactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
        m := by
  simpa [exactZABAffineFeatureERMRecoveryData] using
    (exactZABAffineFeatureERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat samples q hq).recoveryLowerBound i m

theorem exactZABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).toEncodedFamily.BadCodes
            ((exactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i),
          agreementMass μ
            ((exactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
            ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p * ((r + (k + k)) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ
        ((exactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict i)
        m := by
  simpa [exactZABSparseThresholdAffineERMRecoveryData] using
    (exactZABSparseThresholdAffineERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
