import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedABTargetInterface

/-!
# P vs NP grassroots: ERM over shared-basis raw exact `(a, b)` classes

This file applies the generic ERM transport layer to the shared-basis exact raw
`(a, b)` families.

If the wrapper is honestly choosing from one fixed shared affine basis on the
raw exact `(a, b)` bits and one fixed decision-list combiner class, then the
selected code is again the route witness.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The indexed exact-surface family obtained by running ERM inside the shared
raw exact `(a, b)` decision-list class. -/
noncomputable def sharedExactABAffineDecisionListERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABAffineDecisionListBitFamily Z features).indexedEmpiricalRiskFamily samples

theorem sharedExactABAffineDecisionListERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let code : SharedAffineDecisionListCode r :=
    (sharedAffineDecisionListCodeEquivBitCode r).symm
      ((sharedExactABAffineDecisionListBitFamily Z features).empiricalRiskCode (samples i))
  calc
    (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]
    _ = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]

theorem sharedExactABAffineDecisionListERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABAffineDecisionListFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let code : SharedAffineDecisionListCode r :=
    (sharedAffineDecisionListCodeEquivBitCode r).symm
      ((sharedExactABAffineDecisionListBitFamily Z features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext x
  change
    (sharedExactABAffineDecisionListERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABAffineDecisionListPredict (r := r) (k := k) features code x
  calc
    (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]
    _ = sharedABAffineDecisionListPredict (r := r) (k := k) features code
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABAffineDecisionListPredict (r := r) (k := k) features code x := by
          cases x
          rfl

def sharedExactABAffineDecisionListERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABAffineDecisionListERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABAffineDecisionListERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineDecisionListERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (r + 1) := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABAffineDecisionListERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABAffineDecisionListERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

section

variable [Inhabited Z] [Fintype Z]

theorem sharedExactABAffineDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q) :
    SharedABDecisionListRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨?_, ?_, hq⟩
  · exact
      sharedExactABAffineDecisionListERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABAffineDecisionListERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  exact
    (sharedExactABAffineDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
