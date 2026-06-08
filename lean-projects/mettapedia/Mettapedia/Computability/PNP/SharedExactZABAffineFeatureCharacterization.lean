import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction
import Mettapedia.Computability.PNP.SharedExactZABFeatureFamilies

/-!
# P vs NP route characterization: shared exact affine features are exactly an
  injective summary route

The shared exact affine-feature branch is the strongest optimistic exact-ZAB
route: once one shared extractor `zfeat` and one shared affine basis are fixed,
the downstream combiner is an arbitrary truth table on the shared feature
summary.

This file records the precise boundary of that optimism.

* If the shared affine summary is injective on the exact visible surface, then
  the branch realizes the full exact Boolean rule family.
* If the shared affine summary is not injective, then every predictor in the
  branch is constant on some summary collision fiber, so the branch cannot be
  surjective onto the full exact rule family.

So this route is not a compression theorem in disguise.  It is exactly an
injective-codebook requirement on the shared summary map.
-/

namespace Mettapedia.Computability.PNP

section SummaryInvariant

variable {Z : Type*} {p r k : ℕ}

/-- A rule is summary-invariant if it depends only on one visible summary map. -/
def ExactVisibleSummaryInvariantRule
    (summary : ExactVisiblePostSwitchSurface Z k → BitVec p)
    (rule : ExactVisibleRule Z k) : Prop :=
  ∀ u v, summary u = summary v → rule u = rule v

theorem not_surjective_predict_of_all_exactVisibleSummaryInvariant
    {Index : Type*}
    {summary : ExactVisiblePostSwitchSurface Z k → BitVec p}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv :
      ∀ i, ExactVisibleSummaryInvariantRule
        (Z := Z) (p := p) (k := k) summary (G.predict i))
    (hni : ¬ Function.Injective summary) :
    ¬ Function.Surjective G.predict := by
  classical
  rw [Function.Injective] at hni
  push_neg at hni
  rcases hni with ⟨u, v, huv, hne⟩
  let rule : ExactVisibleRule Z k := fun x => if x = u then true else false
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hrule :
      ExactVisibleSummaryInvariantRule
        (Z := Z) (p := p) (k := k) summary rule := by
    intro x y hxy
    simpa [hi] using hinv i x y hxy
  have hconst : rule u = rule v := hrule u v huv
  have hvu : v = u := by
    simpa [rule] using hconst
  exact hne hvu.symm

theorem all_exactVisibleSummaryInvariant_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i,
      ExactVisibleSummaryInvariantRule
        (Z := Z) (p := p) (k := k)
        (exactZABAffineFeatureSummary
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)
        (G.predict i) := by
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
            have hidx :
                (Fintype.equivFinOfCardEq
                  (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p))
                    (exactZABAffineFeatureSummary
                      (Z := Z) (p := p) (r := r) (k := k) zfeat features u) =
                  (Fintype.equivFinOfCardEq
                    (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p))
                    (exactZABAffineFeatureSummary
                      (Z := Z) (p := p) (r := r) (k := k) zfeat features v) :=
              congrArg
                (Fintype.equivFinOfCardEq
                  (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p))
                huv
            simpa [sharedExactZABAffineFeaturePredict] using congrArg table hidx
    _ = G.predict i v := by
            simp [htable]

theorem injective_summary_of_surjective_predict_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Function.Injective
      (exactZABAffineFeatureSummary
        (Z := Z) (p := p) (r := r) (k := k) zfeat features) := by
  by_contra hni
  exact
    (not_surjective_predict_of_all_exactVisibleSummaryInvariant
      (Z := Z) (p := p) (k := k)
      (summary := exactZABAffineFeatureSummary
        (Z := Z) (p := p) (r := r) (k := k) zfeat features)
      (G := G)
      (all_exactVisibleSummaryInvariant_of_realizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni) hsurj

end SummaryInvariant

section FullRuleFamily

variable {Z : Type*} {p r k : ℕ} [Fintype Z]

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_of_injective_summary
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hinj :
      Function.Injective
        (exactZABAffineFeatureSummary
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)) :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k)
      zfeat features (fullExactVisibleRuleFamily Z k) := by
  classical
  intro rule
  let summary :=
    exactZABAffineFeatureSummary (Z := Z) (p := p) (r := r) (k := k) zfeat features
  let lookup : BitVec p → Bool := fun code =>
    if h : ∃ u, summary u = code then
      rule (Classical.choose h)
    else
      false
  let table : BitCode (2 ^ p) := fun idx =>
    lookup
      ((Fintype.equivFinOfCardEq
        (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p)).symm idx)
  refine ⟨table, ?_⟩
  funext u
  symm
  change table
      ((Fintype.equivFinOfCardEq
        (by simp [BitVec] : Fintype.card (BitVec p) = 2 ^ p)) (summary u)) =
    rule u
  dsimp [table]
  have hlookup : lookup (summary u) = rule u := by
    dsimp [lookup]
    split_ifs with h
    · have hchoose : Classical.choose h = u := by
        apply hinj
        exact Classical.choose_spec h
      simp [hchoose]
    · exfalso
      exact h ⟨u, rfl⟩
  simpa using hlookup

omit [Fintype Z] in
theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineFeatureFamily_of_not_injective_summary
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hni :
      ¬ Function.Injective
        (exactZABAffineFeatureSummary
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)) :
    ¬ RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily Z k) := by
  intro hreal
  exact
    hni
      (injective_summary_of_surjective_predict_of_realizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k)
        (G := fullExactVisibleRuleFamily Z k)
        hreal (fullExactVisibleRuleFamily_surjective Z k))

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_iff_injective_summary
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily Z k) ↔
      Function.Injective
        (exactZABAffineFeatureSummary
          (Z := Z) (p := p) (r := r) (k := k) zfeat features) := by
  constructor
  · intro hreal
    exact
      injective_summary_of_surjective_predict_of_realizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k)
        (G := fullExactVisibleRuleFamily Z k)
        hreal (fullExactVisibleRuleFamily_surjective Z k)
  · intro hinj
    exact
      fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_of_injective_summary
        (Z := Z) (p := p) (r := r) (k := k) zfeat features hinj

end FullRuleFamily

end Mettapedia.Computability.PNP
