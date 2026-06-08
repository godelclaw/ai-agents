import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData

/-!
# P vs NP route obstruction: manuscript-facing sparse-threshold recovery packets
  already force a finite predictor quotient

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData` does more than
package an agreement estimate.  It automatically yields a finite
predictor-quotient presentation of the actual switched family at point-block
budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`.

This file turns that exact quotient consequence back against the manuscript
route.  Any injectively realized finite probe family on the exact visible
surface must already fit inside that quotient budget.  So the route cannot
rescue recovery merely by asking for a small quotient-code presentation instead
of surjectivity onto the full Boolean rule space.
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

/-- Recovery data already forces every injectively realized finite probe family
to fit inside the current point-block predictor-quotient budget. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.card_le_pointBlockQuotientBudget_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, T.predictorFamily.predict i = target p) :
    Fintype.card Probe ≤
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) := by
  exact
    exactVisible_finitePredictorQuotient_card_le_of_injective_realization
      target hinj hreal h.finitePredictorQuotient

/-- In particular, if the actual predictor family is injective on a finite
index type, then recovery already bounds the number of actual indices by the
current point-block quotient budget. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.indexCard_le_pointBlockQuotientBudget_of_injective_predict
    [Fintype Index]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective T.predictorFamily.predict) :
    Fintype.card Index ≤
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) := by
  exact
    h.card_le_pointBlockQuotientBudget_of_injective_realization
      (Probe := Index)
      (target := T.predictorFamily.predict)
      hinj
      (by
        intro i
        exact ⟨i, rfl⟩)

/-- Therefore no manuscript-facing recovery packet can exist if the actual
switched family already realizes an injective finite probe family larger than
the current point-block quotient budget. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_pointBlockQuotientBudget_lt_card
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
  exact Nat.not_le_of_lt hs <|
    h.card_le_pointBlockQuotientBudget_of_injective_realization
      target hinj hreal

/-- The same quotient obstruction already removes the extractor choice itself:
if the actual switched family realizes an injective finite probe family larger
than the current point-block quotient budget, then no extractor at all can
support the manuscript-facing recovery packet. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_pointBlockQuotientBudget_lt_card
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
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_pointBlockQuotientBudget_lt_card
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      (target := target)
      hinj
      hreal
      hs
      hdata

/-- Likewise, if the actual predictor map is injective on a finite index type,
recovery is impossible once the index cardinality exceeds the point-block
quotient budget. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_pointBlockQuotientBudget_lt_indexCard
    [Fintype Index]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective T.predictorFamily.predict)
    (hs :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) <
        Fintype.card Index) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hs <|
    h.indexCard_le_pointBlockQuotientBudget_of_injective_predict hinj

/-- So an injective finite-index actual switched family whose index cardinality
already exceeds the point-block quotient budget cannot be rescued by changing
the extractor: no extractor at all can support the manuscript-facing recovery
packet. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_pointBlockQuotientBudget_lt_indexCard
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
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_pointBlockQuotientBudget_lt_indexCard
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hinj
      hs
      hdata

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
