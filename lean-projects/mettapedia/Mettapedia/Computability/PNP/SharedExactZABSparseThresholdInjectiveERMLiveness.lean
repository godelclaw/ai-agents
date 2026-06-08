import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdInjectiveLiveness
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.BitFamilyUniformRecovery

/-!
# P vs NP route liveness: injective exact `z+a+b` sparse-threshold ERM routes
  can realize the full rule family

`SharedExactZABSparseThresholdInjectiveLiveness.lean` proved that the shared
exact sparse-threshold class itself is fully expressive whenever the exact
visible summary `(z,a,b) ↦ (zfeat(z),a,b)` is injective.

This file upgrades that class-level statement to an actual ERM-family
statement.  Under the standard finite counting gap, every target Boolean rule on
the exact surface admits one labeled point sample on which ERM over the shared
point-block sparse-threshold family recovers that target exactly.  Choosing one
such sample for each target rule yields a single sample-indexed ERM family equal
to `fullExactVisibleRuleFamily`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} [Fintype Z] {r k m : ℕ}

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_exactZABVisibleData
    (zfeat : Z → BitVec r)
    (hinj :
      Function.Injective (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat))
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    ∃ samples :
        ExactVisibleRule Z k →
          Sample (ExactVisiblePostSwitchSurface Z k) Bool,
        sharedExactZABSparseThresholdAffineERMFamily
            (Z := Z)
            (p := allAffinePointBlockFeatureCount (r + (k + k)))
            (r := r) (k := k)
            (Index := ExactVisibleRule Z k)
            zfeat
            (allAffinePointBlockFeatures (r + (k + k)))
            samples =
          fullExactVisibleRuleFamily Z k := by
  classical
  let F :=
    sharedExactZABSparseThresholdAffineBitFamily
      Z zfeat (allAffinePointBlockFeatures (r + (k + k)))
  have hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))
        (fullExactVisibleRuleFamily Z k) :=
    fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_exactZABVisibleData
      (Z := Z) (r := r) (k := k) zfeat hinj hwidth
  have htarget :
      ∀ rule : ExactVisibleRule Z k,
        ∃ c : BitCode (2 * allAffinePointBlockFeatureCount (r + (k + k))),
          F.decode c = rule := by
    intro rule
    rcases hreal rule with ⟨code, hcode⟩
    refine
      ⟨sharedSparseThresholdCodeEquivBitCode
          (allAffinePointBlockFeatureCount (r + (k + k))) code, ?_⟩
    calc
      F.decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code)
        =
          sharedExactZABSparseThresholdAffinePredict
            (Z := Z)
            (p := allAffinePointBlockFeatureCount (r + (k + k)))
            (r := r) (k := k)
            zfeat
            (allAffinePointBlockFeatures (r + (k + k))) code := by
              simp [F]
      _ = (fullExactVisibleRuleFamily Z k).predict rule := hcode.symm
      _ = rule := rfl
  let pointSamples : ExactVisibleRule Z k → PointSample (ExactVisiblePostSwitchSurface Z k) m :=
    fun rule =>
      Classical.choose
        (F.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
          rule m (htarget rule) hbound)
  let samples :
      ExactVisibleRule Z k → Sample (ExactVisiblePostSwitchSurface Z k) Bool :=
    fun rule => labeledByTarget rule (pointSamples rule)
  refine ⟨samples, ?_⟩
  cases hERM :
      sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        (Index := ExactVisibleRule Z k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))
        samples with
  | mk predictERM =>
      cases hFull : fullExactVisibleRuleFamily Z k with
      | mk predictFull =>
          have hpredict : predictERM = predictFull := by
            funext rule u
            have hfit :
                F.empiricalRiskPredictor (samples rule) = rule := by
              simpa [samples, pointSamples] using
                Classical.choose_spec
                  (F.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
                    rule m (htarget rule) hbound)
            have hERM_eval :
                F.empiricalRiskPredictor (samples rule) u = predictERM rule u := by
              simpa [sharedExactZABSparseThresholdAffineERMFamily,
                BitEncodedClassifierFamily.indexedEmpiricalRiskFamily] using
                congrFun
                  (congrFun (congrArg IndexedPredictorFamily.predict hERM) rule) u
            have hFull_eval : rule u = predictFull rule u := by
              simpa [fullExactVisibleRuleFamily] using
                congrFun
                  (congrFun (congrArg IndexedPredictorFamily.predict hFull) rule) u
            calc
              predictERM rule u
                =
                  F.empiricalRiskPredictor (samples rule) u := by
                    exact hERM_eval.symm
              _ = rule u := congrFun hfit u
              _ = predictFull rule u := by
                    exact hFull_eval
          cases hpredict
          rfl

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_zfeat
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    ∃ samples :
        ExactVisibleRule Z k →
          Sample (ExactVisiblePostSwitchSurface Z k) Bool,
        sharedExactZABSparseThresholdAffineERMFamily
            (Z := Z)
            (p := allAffinePointBlockFeatureCount (r + (k + k)))
            (r := r) (k := k)
            (Index := ExactVisibleRule Z k)
            zfeat
            (allAffinePointBlockFeatures (r + (k + k)))
            samples =
          fullExactVisibleRuleFamily Z k := by
  exact
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_exactZABVisibleData
      (Z := Z) (r := r) (k := k) (m := m) zfeat
      (exactZABVisibleData_injective_of_injective_zfeat
        (Z := Z) (r := r) (k := k) zfeat hinj)
      hwidth hbound

end

end Mettapedia.Computability.PNP
