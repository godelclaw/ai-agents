import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstruction
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction

/-!
# P vs NP crux: widened injective exact-ZAB ERM routes still miss the full rule class

`ExactZABInjectiveBranchObstruction.lean` proves that surjectivity on the raw
exact/shared exact `z+a+b` ERM surfaces already forces large extractor or
combiner parameters, even when the `z`-extractor is injective.

This file turns those lower bounds into direct route contradictions on the
named target family `fullExactVisibleRuleFamily`.  Below the verified lower
bounds, there is no choice of samples that makes the ERM-selected family equal
to the full exact-visible Boolean rule class.
-/

namespace Mettapedia.Computability.PNP

section

variable {n p r k : ℕ}

theorem not_exists_exactZABDecisionListERMFamily_eq_fullExactVisibleRuleFamily_of_extractorWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec n) k →
          Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool,
        exactZABDecisionListERMFamily
            (Z := BitVec n) (r := r) (k := k)
            (Index := ExactVisibleRule (BitVec n) k)
            zfeat samples =
          fullExactVisibleRuleFamily (BitVec n) k := by
  rintro ⟨samples, hEq⟩
  have hsurj :
      Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k)
          (Index := ExactVisibleRule (BitVec n) k)
          zfeat samples).predict := by
    rw [hEq]
    exact fullExactVisibleRuleFamily_surjective (BitVec n) k
  exact
    (exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
      (n := n) (r := r) (k := k) (Index := ExactVisibleRule (BitVec n) k)
      zfeat samples hgap) hsurj

theorem not_exists_sharedExactZABAffineFeatureERMFamily_eq_fullExactVisibleRuleFamily_of_featureCount_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hfeat : p < n + 2 * k) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec n) k →
          Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool,
        sharedExactZABAffineFeatureERMFamily
            (Z := BitVec n) (p := p) (r := r) (k := k)
            (Index := ExactVisibleRule (BitVec n) k)
            zfeat features samples =
          fullExactVisibleRuleFamily (BitVec n) k := by
  rintro ⟨samples, hEq⟩
  have hsurj :
      Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          (Index := ExactVisibleRule (BitVec n) k)
          zfeat features samples).predict := by
    rw [hEq]
    exact fullExactVisibleRuleFamily_surjective (BitVec n) k
  exact
    (sharedExactZABAffineFeatureERMFamily_not_surjective_of_featureCount_lt_visibleWidth
      (n := n) (p := p) (r := r) (k := k) (Index := ExactVisibleRule (BitVec n) k)
      zfeat features samples hfeat) hsurj

theorem not_exists_sharedExactZABAffineDecisionListERMFamily_eq_fullExactVisibleRuleFamily_of_combinerWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hgap : p < 2 ^ (n + 2 * k) - 1) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec n) k →
          Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool,
        sharedExactZABAffineDecisionListERMFamily
            (Z := BitVec n) (p := p) (r := r) (k := k)
            (Index := ExactVisibleRule (BitVec n) k)
            zfeat features samples =
          fullExactVisibleRuleFamily (BitVec n) k := by
  rintro ⟨samples, hEq⟩
  have hsurj :
      Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          (Index := ExactVisibleRule (BitVec n) k)
          zfeat features samples).predict := by
    rw [hEq]
    exact fullExactVisibleRuleFamily_surjective (BitVec n) k
  exact
    (sharedExactZABAffineDecisionListERMFamily_not_surjective_of_combinerWidth_lt_truthTableGap
      (n := n) (p := p) (r := r) (k := k) (Index := ExactVisibleRule (BitVec n) k)
      zfeat features samples hgap) hsurj

end

end Mettapedia.Computability.PNP
