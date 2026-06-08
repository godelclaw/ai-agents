import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstruction
import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdInjectiveERMLiveness

/-!
# P vs NP route characterization: shared exact sparse-threshold ERM is exactly
  an injective-extractor route

The shared exact sparse-threshold point-block route now has both halves
formalized separately:

* `ExactZABVisibleCollisionObstruction.lean` shows that noninjective extractors
  force every predictor in the route to collapse one exact-visible fiber, so no
  such ERM family can be surjective onto the full exact rule family.
* `SharedExactZABSparseThresholdInjectiveERMLiveness.lean` shows that once the
  visible map `(z,a,b) ↦ (zfeat(z),a,b)` is injective and the standard finite
  counting gap holds, there exist samples making the ERM family literally equal
  to `fullExactVisibleRuleFamily`.

This file packages those two facts into one route-facing characterization.
Under the point-block basis and the finite counting gap, the sparse-threshold
ERM route is alive exactly when `zfeat` is injective.
-/

namespace Mettapedia.Computability.PNP

section VisibleData

variable {Z : Type*} {r k : ℕ}

theorem injective_zfeat_of_injective_exactZABVisibleData
    (zfeat : Z → BitVec r)
    (hinj :
      Function.Injective
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat)) :
    Function.Injective zfeat := by
  intro z0 z1 hz
  let a : BitVec k := default
  let b : BitVec k := default
  let u : ExactVisiblePostSwitchSurface Z k := ⟨z0, a, b⟩
  let v : ExactVisiblePostSwitchSurface Z k := ⟨z1, a, b⟩
  have huv :
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
        exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v := by
    simp [u, v, exactZABVisibleData, exactABVisibleData, hz]
  have huv' : u = v := hinj huv
  simpa [u, v] using congrArg PostSwitchInput.z huv'

theorem exactZABVisibleData_injective_iff_injective_zfeat
    (zfeat : Z → BitVec r) :
    Function.Injective (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) ↔
      Function.Injective zfeat := by
  constructor
  · exact injective_zfeat_of_injective_exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat
  · exact exactZABVisibleData_injective_of_injective_zfeat (Z := Z) (r := r) (k := k) zfeat

end VisibleData

section ERMRoute

variable {Z : Type*} [Fintype Z] {r k m : ℕ}

theorem injective_zfeat_of_exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily
    (zfeat : Z → BitVec r)
    (hEq :
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
          fullExactVisibleRuleFamily Z k) :
    Function.Injective zfeat := by
  classical
  by_contra hni
  rcases hEq with ⟨samples, hsamples⟩
  have hsurj :
      Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z)
          (p := allAffinePointBlockFeatureCount (r + (k + k)))
          (r := r) (k := k)
          (Index := ExactVisibleRule Z k)
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))
          samples).predict := by
    simpa [hsamples] using fullExactVisibleRuleFamily_surjective Z k
  exact
    (sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k)
      (Index := ExactVisibleRule Z k)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      samples
      hni) hsurj

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_exactZABVisibleData
    (zfeat : Z → BitVec r)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    (∃ samples :
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
        fullExactVisibleRuleFamily Z k) ↔
      Function.Injective
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) := by
  constructor
  · intro hEq
    exact
      (exactZABVisibleData_injective_iff_injective_zfeat
        (Z := Z) (r := r) (k := k) zfeat).2
        (injective_zfeat_of_exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily
          (Z := Z) (r := r) (k := k) zfeat hEq)
  · intro hinj
    exact
      exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_of_injective_exactZABVisibleData
        (Z := Z) (r := r) (k := k) (m := m) zfeat hinj hwidth hbound

theorem exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_zfeat
    (zfeat : Z → BitVec r)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    (∃ samples :
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
        fullExactVisibleRuleFamily Z k) ↔
      Function.Injective zfeat := by
  rw [← exactZABVisibleData_injective_iff_injective_zfeat (Z := Z) (r := r) (k := k) zfeat]
  exact
    exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily_iff_injective_exactZABVisibleData
      (Z := Z) (r := r) (k := k) (m := m) zfeat hwidth hbound

end ERMRoute

end Mettapedia.Computability.PNP
