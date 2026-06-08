import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdERMCharacterization
import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstruction

/-!
# P vs NP route bridge: actual switched-local point-block sparse-threshold ERM data

The sparse-threshold branch is now sharply characterized on the exact visible
surface: under the point-block shared basis, the ERM family equals the full
exact rule family only when the extractor `zfeat` is injective.

This file lifts that fact to the manuscript-facing `ActualSwitchedLocalInterface`.
It packages the concrete claim that the actual local-rule family is exactly one
shared exact sparse-threshold ERM family on the point-block basis, and then
pushes the route consequences through that interface.

So the remaining burden on the actual switched-local sparse-threshold route is
no longer vague:

* if the actual family is surjective and has this data, `zfeat` cannot be
  noninjective;
* if the actual family is literally the full exact rule family and has this
  data, `zfeat` must be injective;
* on `BitVec n`, any width-compressing extractor `BitVec n → BitVec r` with
  `r < n` is therefore impossible for this manuscript-facing route.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- Manuscript-facing data for the point-block shared exact sparse-threshold ERM
route: the actual local predictor family is exactly one shared exact
sparse-threshold ERM family on the canonical point-block basis
`allAffinePointBlockFeatures (r + 2k)`. -/
structure SharedExactZABSparseThresholdERMData
    {r : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    T.predictorFamily =
      sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))
        samples

namespace SharedExactZABSparseThresholdERMData

variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {zfeat : Z → BitVec r}

theorem targetData
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k) (Index := Index)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      T.predictorFamily := by
  simpa [h.exact_family] using
    sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k) (Index := Index)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      h.samples

theorem not_surjective_predict_of_not_injective_zfeat
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  simpa [h.exact_family] using
    sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k) (Index := Index)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      h.samples
      hni

end SharedExactZABSparseThresholdERMData

section ExactRuleIndex

variable {T : ActualSwitchedLocalInterface Z k (ExactVisibleRule Z k) Block} {r : ℕ}
variable {zfeat : Z → BitVec r}

theorem injective_zfeat_of_eq_fullExactVisibleRuleFamily
    [Fintype Z]
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hfull : T.predictorFamily = fullExactVisibleRuleFamily Z k) :
    Function.Injective zfeat := by
  exact
    injective_zfeat_of_exists_samples_sharedExactZABSparseThresholdAffineERMFamily_eq_fullExactVisibleRuleFamily
      (Z := Z) (r := r) (k := k)
      zfeat
      ⟨h.samples, h.exact_family.symm.trans hfull⟩

theorem not_eq_fullExactVisibleRuleFamily_of_not_injective_zfeat
    [Fintype Z]
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hni : ¬ Function.Injective zfeat) :
    T.predictorFamily ≠ fullExactVisibleRuleFamily Z k := by
  intro hfull
  exact hni (injective_zfeat_of_eq_fullExactVisibleRuleFamily h hfull)

end ExactRuleIndex

section Obstruction

variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {zfeat : Z → BitVec r}

theorem not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_not_injective_zfeat
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  rintro ⟨h⟩
  exact h.not_surjective_predict_of_not_injective_zfeat hni hsurj

theorem not_nonempty_sharedExactZABSparseThresholdERMData_of_eq_fullExactVisibleRuleFamily_of_not_injective_zfeat
    [Fintype Z]
    (T : ActualSwitchedLocalInterface Z k (ExactVisibleRule Z k) Block)
    (zfeat : Z → BitVec r)
    (hfull : T.predictorFamily = fullExactVisibleRuleFamily Z k)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  rintro ⟨h⟩
  exact hni (injective_zfeat_of_eq_fullExactVisibleRuleFamily h hfull)

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_not_injective_zfeat
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_not_injective_zfeat
      (fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hni

end Obstruction

section BitVec

variable {n k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {zfeat : BitVec n → BitVec r}

theorem SharedExactZABSparseThresholdERMData.not_surjective_predict_of_width_lt
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hwidth : r < n) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact
    h.not_surjective_predict_of_not_injective_zfeat
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_width_lt
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hwidth : r < n) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_not_injective_zfeat
      T zfeat hsurj
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (hwidth : r < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_width_lt
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hwidth

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
