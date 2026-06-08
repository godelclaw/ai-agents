import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterface

/-!
# P vs NP grassroots: ERM over shared-basis exact `(zfeat(z), a, b)` features

This file applies the generic ERM transport layer to the shared-basis exact
`z+a+b` affine-feature and sparse-threshold classes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

/-- ERM inside the shared exact `(zfeat(z), a, b)` affine-feature class. -/
noncomputable def sharedExactZABAffineFeatureERMFamily
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactZABAffineFeatureBitFamily Z zfeat features).indexedEmpiricalRiskFamily samples

/-- ERM inside the shared exact `(zfeat(z), a, b)` sparse-threshold class. -/
noncomputable def sharedExactZABSparseThresholdAffineERMFamily
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).indexedEmpiricalRiskFamily samples

theorem sharedExactZABAffineFeatureERMTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) := by
  refine ⟨?_⟩
  intro i
  let table : BitCode (2 ^ p) :=
    (sharedExactZABAffineFeatureBitFamily Z zfeat features).empiricalRiskCode (samples i)
  refine ⟨table, ?_⟩
  funext u
  simp [sharedExactZABAffineFeatureERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    table,
    sharedExactZABAffineFeatureBitFamily]

theorem sharedExactZABSparseThresholdAffineERMTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) := by
  refine ⟨?_⟩
  intro i
  let code : SharedSparseThresholdCode p :=
    (sharedSparseThresholdCodeEquivBitCode p).symm
      ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  simp [sharedExactZABSparseThresholdAffineERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    code,
    sharedExactZABSparseThresholdAffineBitFamily,
    sharedSparseThresholdCodeEquivBitCode]

theorem sharedExactZABAffineFeatureERMCompressionTarget
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples)
      (2 ^ p) := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).compressionTarget

theorem sharedExactZABSparseThresholdAffineERMCompressionTarget
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples)
      (2 * p) := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).compressionTarget

theorem sharedExactZABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).surfaceCard_le_of_surjective_predict hsurj

theorem sharedExactZABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * p := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).surfaceCard_le_of_surjective_predict hsurj

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).not_surjective_predict_of_lt_surfaceCard hs

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 * p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).not_surjective_predict_of_lt_surfaceCard hs

section

variable [Fintype Z]

def sharedExactZABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q) :
    SharedExactZABAffineFeatureRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) q := by
  refine ⟨features, ?_, hq⟩
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).realized

def sharedExactZABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q) :
    SharedExactZABSparseThresholdRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) q := by
  refine ⟨features, ?_, hq⟩
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).realized

theorem sharedExactZABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ
        ((sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
        m := by
  simpa [sharedExactZABAffineFeatureERMRecoveryData] using
    (sharedExactZABAffineFeatureERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features samples q hq).recoveryLowerBound i m

theorem sharedExactZABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ
        ((sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
        m := by
  simpa [sharedExactZABSparseThresholdAffineERMRecoveryData] using
    (sharedExactZABSparseThresholdAffineERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
