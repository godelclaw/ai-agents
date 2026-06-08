import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData

/-!
# P vs NP route obstruction: manuscript-facing sparse-threshold recovery packets
  already force a finite-learning payload

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData` does more than
package an agreement estimate.  It automatically yields an exact-visible
compression target and therefore the full current clocked finite-learning
payload at point-block budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`.

This file turns that observation back against the manuscript-facing route.
Whenever the actual switched predictor family is still too expressive for that
payload budget, no sparse-threshold recovery packet can exist:

* if the family is surjective onto all Boolean rules on the exact visible
  surface, recovery data is impossible below the corresponding predictor-space
  cardinality;
* more generally, if the family already realizes an injectively indexed finite
  probe family larger than the current payload budget, recovery data is again
  impossible.

So the route cannot appeal to finite-learning / good-sample consequences unless
it first proves a genuinely small predictor image.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- If the actual switched predictor family is still fully expressive on the
exact visible surface, then the manuscript-facing sparse-threshold recovery
packet is impossible below the corresponding predictor-space cardinality. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact
    not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z)
      (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (clock := 0)
      (Index := Index)
      hs
      hsurj
      (h.clockedKpolyFiniteLearningPayload (clock := 0))

/-- The same payload obstruction already removes the extractor choice: if the
actual switched predictor family is still fully expressive on the exact visible
surface, then below the corresponding predictor-space cardinality no extractor
at all can support the manuscript-facing sparse-threshold recovery packet. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      (q := q)
      hs
      hsurj
      hdata

/-- More generally, any injectively realized finite probe family larger than the
current point-block payload budget already blocks the manuscript-facing recovery
packet. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, T.predictorFamily.predict i = target p)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Probe) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact
    not_clockedKpolyFiniteLearningPayload_of_injective_realization_of_lt_card
      (Z := Z)
      (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (clock := 0)
      (Index := Index)
      target
      hinj
      hreal
      hs
      (h.clockedKpolyFiniteLearningPayload (clock := 0))

/-- Likewise, any injectively realized finite probe family larger than the
current payload budget already removes the extractor choice itself: no
extractor can support the manuscript-facing recovery packet on that actual
switched family. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, T.predictorFamily.predict i = target p)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Probe) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      (target := target)
      hinj
      hreal
      hs
      hdata

/-- If the actual switched predictor family itself is injective on a finite
index type, then the manuscript-facing recovery packet already forces the
actual predictor family to contain at most `2^(2 * allAffinePointBlockFeatureCount (r + 2*k))`
distinct indices. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_lt_indexCard
    [Fintype Index]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective T.predictorFamily.predict)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Index) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := μ)
      (T := T)
      (r := r)
      (zfeat := zfeat)
      (Probe := Index)
      (target := T.predictorFamily.predict)
      hinj
      (by
        intro i
        exact ⟨i, rfl⟩)
      hs

/-- So an injective finite-index actual switched family whose index cardinality
already exceeds the current payload budget cannot be rescued by changing the
extractor: no extractor at all can support the manuscript-facing recovery
packet. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_lt_indexCard
    [Fintype Index]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hinj : Function.Injective T.predictorFamily.predict)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Index) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_lt_indexCard
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hinj
      hs
      hdata

/-- Full-rule specialization: the manuscript-facing sparse-threshold recovery
packet cannot exist once the point-block finite-learning payload budget is
strictly below the full exact visible Boolean predictor-space cardinality. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
    (zfeat : Z → BitVec r)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      hs
      (fullRuleActualSwitchedLocalInterface_surjective Z k)

/-- The full-rule manuscript-facing sparse-threshold recovery route also cannot
evade this payload obstruction by changing the extractor: once the current
payload budget is strictly below the full exact visible Boolean predictor-space
cardinality, no extractor at all can support the packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface Z k)
            zfeat
            q) := by
  exact
    not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_predictorCard
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      (q := q)
      hs
      (fullRuleActualSwitchedLocalInterface_surjective Z k)

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
