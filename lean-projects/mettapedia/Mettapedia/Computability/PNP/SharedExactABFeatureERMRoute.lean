import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedABRecoveryInterface

/-!
# P vs NP grassroots: ERM over shared-basis raw exact `(a, b)` feature classes

This file applies the generic ERM transport layer to the shared-basis exact raw
`(a, b)` affine-feature and sparse-threshold classes.

If the wrapper is honestly choosing from one fixed shared affine basis on the
raw exact `(a, b)` bits and one fixed downstream combiner class, then the
selected ERM code is again the route witness.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- ERM inside the shared raw exact `(a, b)` affine-feature class. -/
noncomputable def sharedExactABAffineFeatureERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABAffineFeatureBitFamily Z features).indexedEmpiricalRiskFamily samples

/-- ERM inside the shared raw exact `(a, b)` sparse-threshold class. -/
noncomputable def sharedExactABSparseThresholdAffineERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABSparseThresholdAffineBitFamily Z features).indexedEmpiricalRiskFamily samples

theorem sharedExactABAffineFeatureERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let table : BitCode (2 ^ r) :=
    (sharedExactABAffineFeatureBitFamily Z features).empiricalRiskCode (samples i)
  calc
    (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table u := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]
    _ = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]

theorem sharedExactABSparseThresholdAffineERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let code : SharedSparseThresholdCode r :=
    (sharedSparseThresholdCodeEquivBitCode r).symm
      ((sharedExactABSparseThresholdAffineBitFamily Z features).empiricalRiskCode (samples i))
  calc
    (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]
    _ = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]

theorem sharedExactABAffineFeatureERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABAffineFeatureFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let table : BitCode (2 ^ r) :=
    (sharedExactABAffineFeatureBitFamily Z features).empiricalRiskCode (samples i)
  refine ⟨table, ?_⟩
  funext x
  change
    (sharedExactABAffineFeatureERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABAffineFeaturePredict (r := r) (k := k) features table x
  calc
    (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]
    _ = sharedABAffineFeaturePredict (r := r) (k := k) features table
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features table)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABAffineFeaturePredict (r := r) (k := k) features table x := by
          cases x
          rfl

theorem sharedExactABSparseThresholdAffineERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABSparseThresholdAffineFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let code : SharedSparseThresholdCode r :=
    (sharedSparseThresholdCodeEquivBitCode r).symm
      ((sharedExactABSparseThresholdAffineBitFamily Z features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext x
  change
    (sharedExactABSparseThresholdAffineERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABSparseThresholdAffinePredict (r := r) (k := k) features code x
  calc
    (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]
    _ = sharedABSparseThresholdAffinePredict (r := r) (k := k) features code
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABSparseThresholdAffinePredict (r := r) (k := k) features code x := by
          cases x
          rfl

def sharedExactABAffineFeatureERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABAffineFeatureTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABAffineFeatureERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABAffineFeatureERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

def sharedExactABSparseThresholdAffineERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABSparseThresholdAffineERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABSparseThresholdAffineERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineFeatureERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (2 ^ r) := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABSparseThresholdAffineERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (2 * r) := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

theorem sharedExactABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Inhabited Z] [Fintype Z]

def sharedExactABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q) :
    SharedABAffineFeatureRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨features, ?_, ?_, hq⟩
  · exact
      sharedExactABAffineFeatureERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABAffineFeatureERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

def sharedExactABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q) :
    SharedABSparseThresholdRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨features, ?_, ?_, hq⟩
  · exact
      sharedExactABSparseThresholdAffineERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABSparseThresholdAffineERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineFeatureBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  simpa [sharedExactABAffineFeatureERMRecoveryData] using
    (sharedExactABAffineFeatureERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

theorem sharedExactABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  simpa [sharedExactABSparseThresholdAffineERMRecoveryData] using
    (sharedExactABSparseThresholdAffineERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
