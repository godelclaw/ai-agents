import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction

/-!
# P vs NP route obstruction: manuscript-facing sparse-threshold recovery data
  still faces the unconditional visible-budget obstruction

`ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction`
already shows that surjective actual-local shared exact sparse-threshold ERM
data must fit the exact visible surface inside the point-block bit budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`.

This file records the same consequence directly at the manuscript-facing
recovery layer.  No recovery-threshold estimate and no finite counting-gap
hypothesis are used: recovery data contains the exact-family data, so the same
unconditional half-width obstruction already applies to the full recovery
packet.

On `BitVec n`, any surjective manuscript-facing recovery packet therefore
forces

* `n ≤ 2*r + 2*k + 1`,

and the full-rule / bounded-sample endpoints are impossible below that
threshold.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {zfeat : BitVec n → BitVec r} {q : ℝ≥0∞}

/-- Surjective actual-local shared exact sparse-threshold recovery data on
`BitVec n` inherits the same unconditional visible-width ceiling as the
underlying exact-family data packet. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    n ≤ 2 * r + 2 * k + 1 := by
  exact
    h.data.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      hsurj

/-- The full-rule manuscript-facing recovery endpoint already faces the same
unconditional half-width obstruction. -/
theorem visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
    (h :
      Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)

/-- The bounded-sample manuscript-facing recovery endpoint inherits the same
unconditional half-width obstruction once the sample bound is large enough for
surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    {sampleBound : ℕ}
    (h :
      Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q))
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)

/-- Therefore no surjective `BitVec n` actual-local family can carry
manuscript-facing shared exact sparse-threshold recovery data once the
extractor width is below the unconditional point-block visible-budget
threshold. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hgap <|
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      hsurj

/-- The same visible-budget obstruction already removes the extractor choice at
the manuscript-facing recovery layer: below the half-width threshold, no
`BitVec n → BitVec r` extractor can support surjective shared exact
sparse-threshold recovery data. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := T) (μ := μ) (zfeat := zfeat) (q := q) hsurj hgap hdata

/-- In particular, the full-rule manuscript-facing recovery endpoint is
excluded on `BitVec n` whenever `2*r + 2*k + 1 < n`. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := n)
      (k := k)
      (r := r)
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      (μ := μ)
      (zfeat := zfeat)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

/-- So the full-rule manuscript-facing recovery route cannot evade the
unconditional visible-budget obstruction by changing the extractor: below the
half-width threshold, no extractor at all can support the packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec n) k)
            zfeat
            q) := by
  exact
    not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      (μ := μ)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

/-- Likewise, the bounded-sample manuscript-facing recovery endpoint is
excluded below the same unconditional half-width threshold once the sample
bound is large enough for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {sampleBound : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := n)
      (k := k)
      (r := r)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface
        (BitVec n) k sampleBound)
      (μ := μ)
      (zfeat := zfeat)
      (q := q)
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)
      hgap

/-- The bounded-sample manuscript-facing recovery route also cannot evade the
same obstruction by changing the extractor: once the sample bound is large
enough for surjectivity, below the half-width threshold no extractor at all can
support the packet. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {sampleBound : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityActualSwitchedLocalInterface
              (BitVec n) k sampleBound)
            zfeat
            q) := by
  exact
    not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface
        (BitVec n) k sampleBound)
      (μ := μ)
      (q := q)
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)
      hgap

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
