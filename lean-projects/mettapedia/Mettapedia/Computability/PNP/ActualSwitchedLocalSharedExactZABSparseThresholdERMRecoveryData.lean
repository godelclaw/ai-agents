import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMData
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterface

/-!
# P vs NP route bridge: actual switched-local point-block sparse-threshold ERM
  recovery data

`ActualSwitchedLocalSharedExactZABSparseThresholdERMData` already packages the
manuscript-facing claim that one actual switched-local family is exactly one
shared exact sparse-threshold ERM family on the point-block basis.

This file adds the next layer that the manuscript would need for any recovery /
good-sample route: a bad-code agreement bound for that same ERM family.  Once
those data are supplied, the exact-visible compression target, finite predictor
image bounds, clocked `Kpoly` payload, and weighted exact-recovery lower bound
follow automatically for the actual switched-local family.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- Manuscript-facing recovery data for the point-block shared exact
sparse-threshold ERM route: in addition to the exact-family identification, one
also supplies a uniform bad-code agreement bound. -/
structure SharedExactZABSparseThresholdERMRecoveryData
    [Fintype Z]
    {r : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞) where
  data : SharedExactZABSparseThresholdERMData T zfeat
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABSparseThresholdAffineBitFamily
          Z
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))).toEncodedFamily.BadCodes
            (T.predictorFamily.predict i),
        agreementMass μ (T.predictorFamily.predict i)
          ((sharedExactZABSparseThresholdAffineBitFamily
            Z
            zfeat
            (allAffinePointBlockFeatures (r + (k + k)))).decode c.1) ≤ q

namespace SharedExactZABSparseThresholdERMRecoveryData

variable [Fintype Z] {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- Forget the actual-local wrapper and recover the exact-visible shared
sparse-threshold ERM recovery packet. -/
noncomputable def exactVisibleRecoveryData
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    Mettapedia.Computability.PNP.SharedExactZABSparseThresholdERMRecoveryData
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k) (Index := Index)
      μ zfeat T.predictorFamily q where
  features := allAffinePointBlockFeatures (r + (k + k))
  samples := h.data.samples
  exact_family := h.data.exact_family
  agreement_le := h.agreement_le

theorem targetData
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k) (Index := Index)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      T.predictorFamily := by
  exact h.exactVisibleRecoveryData.targetData

theorem compressionTarget
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      T.predictorFamily
      (2 * allAffinePointBlockFeatureCount (r + (k + k))) := by
  exact h.exactVisibleRecoveryData.compressionTarget

theorem finitePredictorCover
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    T.predictorFamily.FinitePredictorCover
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (Index := Index) (G := T.predictorFamily)).1
      h.compressionTarget

theorem finiteIndexRepresentativeCover
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    T.predictorFamily.FiniteIndexRepresentativeCover
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (Index := Index) (G := T.predictorFamily)).1
      h.compressionTarget

theorem finitePredictorQuotient
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    T.predictorFamily.FinitePredictorQuotient
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (Index := Index) (G := T.predictorFamily)).1
      h.compressionTarget

theorem clockedKpolyFiniteLearningPayload
    {clock : ℕ}
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily
      (2 * allAffinePointBlockFeatureCount (r + (k + k)))
      clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (Z := Z) (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (clock := clock) (Index := Index)
      h.compressionTarget

theorem surfaceCard_le_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 * allAffinePointBlockFeatureCount (r + (k + k)) := by
  exact h.exactVisibleRecoveryData.surfaceCard_le_of_surjective_predict hsurj

theorem not_surjective_predict_of_lt_surfaceCard
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact h.exactVisibleRecoveryData.not_surjective_predict_of_lt_surfaceCard hs

theorem recoveryLowerBound
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (i : Index) (m : ℕ) :
    1 -
        (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).bitExactRecoverySampleMass
          μ (T.predictorFamily.predict i) m := by
  exact h.exactVisibleRecoveryData.recoveryLowerBound i m

theorem not_surjective_predict_of_not_injective_zfeat
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact h.data.not_surjective_predict_of_not_injective_zfeat hni

end SharedExactZABSparseThresholdERMRecoveryData

section Obstruction

variable [Fintype Z] {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_injective_zfeat
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact h.data.not_surjective_predict_of_not_injective_zfeat hni hsurj

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_injective_zfeat
      (μ := μ)
      (fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hni

end Obstruction

section BitVec

variable [Fintype (BitVec n)]
variable {n k r : ℕ} {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {zfeat : BitVec n → BitVec r} {q : ℝ≥0∞}

theorem SharedExactZABSparseThresholdERMRecoveryData.not_surjective_predict_of_width_lt
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hwidth : r < n) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    h.not_surjective_predict_of_not_injective_zfeat
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_width_lt
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwidth : r < n) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_injective_zfeat
      (μ := μ) T zfeat hsurj
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (hwidth : r < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_width_lt
      (μ := μ)
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hwidth

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
