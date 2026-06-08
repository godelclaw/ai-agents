import Mettapedia.Computability.PNP.SharedABFeatureObstruction

/-!
# PNP crux: shared `(a,b)` feature routes cannot keep full reduced expressivity

`SharedABFeatureRoutes.lean` supplies three positive route surfaces:

* one shared affine basis with an arbitrary truth-table combiner;
* one shared affine basis with a sparse-threshold combiner;
* one shared affine basis with a fixed-order decision-list combiner.

This file turns those route certificates into direct contradiction theorems.
If the exact family still factors through a fully expressive reduced `(a,b)`
family, then any of the above route assumptions force an exact-visible budget
that is already below the reduced truth-table threshold.  So the named route
assumptions themselves are inconsistent on that branch.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The factor-through shared affine-feature route is inconsistent whenever the
reduced family stays fully expressive and the route budget is below the reduced
truth-table threshold. -/
theorem not_factorsThrough_ab_and_sharedAffineFeature_of_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    False := by
  have hsmall :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) :=
    exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
      (Z := Z) (r := r) (k := k) hfactor hreal
  exact
    (not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k) (s := 2 ^ r) (Index := Index)
      hs hfactor hsurj) hsmall

/-- The factor-through shared sparse-threshold route is inconsistent whenever
the reduced family stays fully expressive and the route budget is below the
reduced truth-table threshold. -/
theorem not_factorsThrough_ab_and_sharedSparseThreshold_of_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    False := by
  have hsmall :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) :=
    exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
      (Z := Z) (r := r) (k := k) hfactor hreal
  exact
    (not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k) (s := 2 * r) (Index := Index)
      hs hfactor hsurj) hsmall

/-- The factor-through shared decision-list route is inconsistent whenever the
reduced family stays fully expressive and the route budget is below the reduced
truth-table threshold. -/
theorem not_factorsThrough_ab_and_sharedDecisionList_of_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    False := by
  have hsmall :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) :=
    exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
      (Z := Z) (r := r) (k := k) hfactor hreal
  exact
    (not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k) (s := r + 1) (Index := Index)
      hs hfactor hsurj) hsmall

section Lift

variable [Inhabited Z]

/-- Invariant-lift contradiction for the shared affine-feature route. -/
theorem not_invariant_and_sharedAffineFeature_of_surjective_lift_of_lt_cardFormula
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < 2 ^ (2 * k))
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Z) (k := k) G).predict)
    (hreal :
      RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    False := by
  exact
    not_factorsThrough_ab_and_sharedAffineFeature_of_surjective_predict_of_lt_cardFormula
      (Z := Z) (r := r) (k := k) hs
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
      hsurj hreal

/-- Invariant-lift contradiction for the shared sparse-threshold route. -/
theorem not_invariant_and_sharedSparseThreshold_of_surjective_lift_of_lt_cardFormula
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < 2 ^ (2 * k))
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Z) (k := k) G).predict)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    False := by
  exact
    not_factorsThrough_ab_and_sharedSparseThreshold_of_surjective_predict_of_lt_cardFormula
      (Z := Z) (r := r) (k := k) hs
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
      hsurj hreal

/-- Invariant-lift contradiction for the shared decision-list route. -/
theorem not_invariant_and_sharedDecisionList_of_surjective_lift_of_lt_cardFormula
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < 2 ^ (2 * k))
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Z) (k := k) G).predict)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    False := by
  exact
    not_factorsThrough_ab_and_sharedDecisionList_of_surjective_predict_of_lt_cardFormula
      (Z := Z) (r := r) (k := k) hs
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
      hsurj hreal

end Lift

end

end Mettapedia.Computability.PNP
