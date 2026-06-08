import Mettapedia.Computability.PNP.ExactZABExtractorCollisionObstruction
import Mettapedia.Computability.PNP.ExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABERMRoute

/-!
# P vs NP crux: noninjective `z` extractors block every exact-visible-summary route

`ExactZABExtractorCollisionObstruction.lean` already kills the raw exact
decision-list route when two latent states share the same visible summary
`(zfeat(z), a, b)`.

This file lifts that collision argument to the broader route surfaces whose
predictors are still functions only of that same visible summary:

* non-shared exact affine-feature / sparse-threshold / affine-decision-list
  families on `(zfeat(z), a, b)`;
* shared-basis exact affine-feature / sparse-threshold / affine-decision-list
  families on `(zfeat(z), a, b)`.

So once `zfeat` is noninjective, no such route can be surjective onto the full
exact rule class, regardless of which downstream combiner family is used.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Core

variable {Z : Type*} {p r k : ℕ}

theorem not_surjective_predict_of_all_exactZABFiberInvariant
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv :
      ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i))
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  classical
  rcases exists_exactZABFiberSeparatingRule_of_not_injective
      (Z := Z) (r := r) (k := k) zfeat hni with ⟨rule, hsep⟩
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hrule :
      ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat rule := by
    simpa [hi] using hinv i
  exact
    (not_exactZABFiberSeparatingRule_of_exactZABFiberInvariantRule
      (Z := Z) (r := r) (k := k) hrule) hsep

theorem all_exactZABFiberInvariant_of_realizedByExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedByExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedByExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨table, htable⟩
  calc
    G.predict i u =
        sharedExactZABAffineFeaturePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features table u := by
            simp [htable]
    _ =
        sharedExactZABAffineFeaturePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features table v := by
            simp [sharedExactZABAffineFeaturePredict, exactZABAffineFeatureSummary, huv]
    _ = G.predict i v := by
            simp [htable]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code u := by
            simp [hcode]
    _ =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code v := by
            simp [sharedExactZABSparseThresholdAffinePredict, huv]
    _ = G.predict i v := by
            simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code u := by
            simp [hcode]
    _ =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code v := by
            simp [sharedExactZABAffineDecisionListPredict, exactZABAffineFeatureSummary, huv]
    _ = G.predict i v := by
            simp [hcode]

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

end Core

section Route

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

theorem ExactZABAffineFeatureTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABAffineFeatureFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem ExactZABSparseThresholdTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABSparseThresholdAffineFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem ExactZABAffineDecisionListTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABAffineDecisionListFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

theorem SharedExactZABSparseThresholdTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

section Recovery

variable [Fintype Z]

theorem ExactZABAffineFeatureRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem ExactZABSparseThresholdRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem ExactZABAffineDecisionListRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABSparseThresholdRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

end Recovery

theorem exactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem exactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

end Route

end Mettapedia.Computability.PNP
