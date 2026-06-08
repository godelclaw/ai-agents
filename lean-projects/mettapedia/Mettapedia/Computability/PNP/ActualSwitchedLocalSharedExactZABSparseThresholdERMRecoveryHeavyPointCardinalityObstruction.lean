import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPairwiseAgreementObstruction
import Mettapedia.Computability.PNP.FiniteIIDAgreement

/-!
# P vs NP route obstruction: a single heavy visible atom collapses any
  manuscript-facing injective recovery family to at most two predictors

The pairwise recovery obstruction says that distinct realized predictors in a
manuscript-facing sparse-threshold recovery packet must have agreement mass at
most `q`.

If some visible point `x` already carries mass `μ x > q`, then two distinct
realized predictors cannot agree at `x`, because that agreement alone would
force agreement mass above `q`.

Since the actual local output is Boolean, evaluation at one such heavy point can
take only two values.  Therefore any injectively indexed actual switched family
supporting the recovery packet must have cardinality at most `2`.

This is a genuine `q`-dependent family-size obstruction.  It does not appeal to
the point-block bit budget, quotient budget, or finite-learning payload.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u}
variable {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- At any visible point heavier than `q`, equality of outputs already forces
global equality of realized predictors in a manuscript-facing sparse-threshold
recovery packet. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.predict_eq_of_apply_eq_of_lt_apply
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    {x : ExactVisiblePostSwitchSurface Z k} {i j : Index}
    (hmass : q < μ x)
    (happly : T.predictorFamily.predict i x = T.predictorFamily.predict j x) :
    T.predictorFamily.predict i = T.predictorFamily.predict j := by
  by_contra hneq
  have hmass_le :
      μ x ≤ agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j) := by
    simpa using
      (finset_mass_le_agreementMass_of_agrees_on
        (μ := μ)
        (target := T.predictorFamily.predict i)
        (predict := T.predictorFamily.predict j)
        ({x} : Finset (ExactVisiblePostSwitchSurface Z k))
        (by
          intro y hy
          have hyx : y = x := by simpa using hy
          simpa [hyx] using happly.symm))
  have hbound :
      agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j) ≤ q := by
    exact
      h.agreementMass_le_of_predict_ne
        (i := i) (j := j)
        (by
          intro hEq
          exact hneq hEq.symm)
  exact not_le_of_gt hmass (le_trans hmass_le hbound)

/-- Therefore an injectively indexed actual switched family can support such a
recovery packet only if it has at most two predictors. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.card_le_two_of_injective_predict_of_lt_apply
    [Fintype Index]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    {x : ExactVisiblePostSwitchSurface Z k}
    (hmass : q < μ x)
    (hinj : Function.Injective T.predictorFamily.predict) :
    Fintype.card Index ≤ 2 := by
  have hpoint_inj : Function.Injective (fun i : Index => T.predictorFamily.predict i x) := by
    intro i j hij
    apply hinj
    exact h.predict_eq_of_apply_eq_of_lt_apply hmass hij
  simpa using Fintype.card_le_of_injective (fun i : Index => T.predictorFamily.predict i x) hpoint_inj

/-- Contrapositive form: if an injectively indexed actual switched family has
more than two predictors and one visible atom already exceeds `q`, then the
manuscript-facing sparse-threshold recovery packet is impossible. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_lt_card_of_injective_predict_of_lt_apply
    [Fintype Index]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective T.predictorFamily.predict)
    {x : ExactVisiblePostSwitchSurface Z k}
    (hmass : q < μ x)
    (hcard : 2 < Fintype.card Index) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hcard (h.card_le_two_of_injective_predict_of_lt_apply hmass hinj)

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
