import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMData

/-!
# P vs NP route characterization: manuscript-facing actual switched-local
  shared exact sparse-threshold ERM data is exactly an injective-extractor
  packet on the full-rule interface

The previous bridge file lifted the sparse-threshold ERM obstruction to the
manuscript-facing `ActualSwitchedLocalInterface`: if one actual switched-local
family is literally a shared exact sparse-threshold ERM family on the canonical
point-block basis, then noninjective extractors already block surjectivity.

This file adds the matching liveness direction on the full-rule actual-local
counterexample.  Under the same point-block width and finite counting gap used
for the ambient ERM route, the full-rule actual switched-local interface carries
such manuscript-facing sparse-threshold ERM data exactly when the extractor is
injective.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

section Generic

variable {Z : Type*} [Fintype Z] {r k m : ℕ} {Index : Type*} {Block : Type*}

theorem nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    Nonempty
      (SharedExactZABSparseThresholdERMData
        T
        zfeat) := by
  classical
  rcases
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_zfeat
      (Z := Z) (r := r) (k := k) (m := m)
      zfeat hinj hwidth hbound with
    ⟨fullSamples, hfull⟩
  let samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool :=
    fun i => fullSamples (T.predictorFamily.predict i)
  refine ⟨{ samples := samples, exact_family := ?_ }⟩
  cases T with
  | mk zOf aOf bOf localRule output output_eq_local =>
      cases hERM :
          sharedExactZABSparseThresholdAffineERMFamily
            (Z := Z)
            (p := allAffinePointBlockFeatureCount (r + (k + k)))
            (r := r) (k := k)
            (Index := Index)
            zfeat
            (allAffinePointBlockFeatures (r + (k + k)))
            samples with
      | mk predictERM =>
          have hpredict : localRule = predictERM := by
            funext i u
            have hERM_eval :
                predictERM i u =
                  (sharedExactZABSparseThresholdAffineERMFamily
                    (Z := Z)
                    (p := allAffinePointBlockFeatureCount (r + (k + k)))
                    (r := r) (k := k)
                    (Index := Index)
                    zfeat
                    (allAffinePointBlockFeatures (r + (k + k)))
                    samples).predict i u := by
              simp [hERM]
            have hfull_eval :
                (sharedExactZABSparseThresholdAffineERMFamily
                  (Z := Z)
                  (p := allAffinePointBlockFeatureCount (r + (k + k)))
                  (r := r) (k := k)
                  (Index := ExactVisibleRule Z k)
                  zfeat
                  (allAffinePointBlockFeatures (r + (k + k)))
                  fullSamples).predict
                    (localRule i) u =
                  localRule i u := by
              simpa [fullExactVisibleRuleFamily] using
                congrFun
                  (congrFun (congrArg IndexedPredictorFamily.predict hfull) (localRule i))
                  u
            calc
              localRule i u
                  =
                    (sharedExactZABSparseThresholdAffineERMFamily
                      (Z := Z)
                      (p := allAffinePointBlockFeatureCount (r + (k + k)))
                      (r := r) (k := k)
                      (Index := ExactVisibleRule Z k)
                      zfeat
                      (allAffinePointBlockFeatures (r + (k + k)))
                      fullSamples).predict
                        (localRule i) u := by
                          exact hfull_eval.symm
              _ =
                    (sharedExactZABSparseThresholdAffineERMFamily
                      (Z := Z)
                      (p := allAffinePointBlockFeatureCount (r + (k + k)))
                      (r := r) (k := k)
                      (Index := Index)
                      zfeat
                      (allAffinePointBlockFeatures (r + (k + k)))
                      samples).predict i u := by
                          simp [samples, sharedExactZABSparseThresholdAffineERMFamily,
                            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
                            ActualSwitchedLocalInterface.predictorFamily]
              _ = predictERM i u := hERM_eval.symm
          cases hpredict
          simp [ActualSwitchedLocalInterface.predictorFamily]

end Generic

section FullRule

variable {Z : Type*} [Fintype Z] {r k m : ℕ}

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    Nonempty
      (SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Z k)
        zfeat) := by
  exact
    nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      hinj
      hwidth
      hbound

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_exactZABVisibleData
    (zfeat : Z → BitVec r)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    Nonempty
      (SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Z k)
        zfeat) ↔
      Function.Injective
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) := by
  constructor
  · rintro ⟨h⟩
    exact
      (exactZABVisibleData_injective_iff_injective_zfeat
        (Z := Z) (r := r) (k := k) zfeat).2 <|
        injective_zfeat_of_eq_fullExactVisibleRuleFamily
          (T := fullRuleActualSwitchedLocalInterface Z k)
          h
          (by simp [fullRuleActualSwitchedLocalInterface_predictorFamily])
  · intro hinj
    exact
      fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
        (Z := Z) (r := r) (k := k) (m := m)
        zfeat
        ((exactZABVisibleData_injective_iff_injective_zfeat
          (Z := Z) (r := r) (k := k) zfeat).1 hinj)
        hwidth hbound

theorem fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat
    (zfeat : Z → BitVec r)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    Nonempty
      (SharedExactZABSparseThresholdERMData
        (fullRuleActualSwitchedLocalInterface Z k)
        zfeat) ↔
      Function.Injective zfeat := by
  constructor
  · rintro ⟨h⟩
    exact
      injective_zfeat_of_eq_fullExactVisibleRuleFamily
        (T := fullRuleActualSwitchedLocalInterface Z k)
        h
        (by simp [fullRuleActualSwitchedLocalInterface_predictorFamily])
  · intro hinj
    exact
      fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
        (Z := Z) (r := r) (k := k) (m := m)
        zfeat hinj hwidth hbound

end FullRule

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
