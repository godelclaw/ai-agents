import Mettapedia.Computability.PNP.SharedABFeatureRouteCrux

/-!
# Regression checks for the shared `(a,b)` feature route crux

These wrappers keep the route-facing contradiction surface compact.
-/

namespace Mettapedia.Computability.PNP.SharedABFeatureRouteCruxRegression

open Mettapedia.Computability.PNP

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Unit 1 Index}
    {features : Fin 1 → AffineColumnCode (1 + 1)}
    (hinv : ABVisibleInvariant (Z := Unit) (k := 1) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Unit) (k := 1) G).predict)
    (hreal :
      RealizedBySharedABAffineFeatureFamily (r := 1) (k := 1) features
        (liftToABVisibleFamily (Z := Unit) (k := 1) G)) :
    False :=
  not_invariant_and_sharedAffineFeature_of_surjective_lift_of_lt_cardFormula
    (Z := Unit) (r := 1) (k := 1) (Index := Index) (by decide) hinv hsurj hreal

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Unit 1 Index}
    {features : Fin 1 → AffineColumnCode (1 + 1)}
    (hinv : ABVisibleInvariant (Z := Unit) (k := 1) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Unit) (k := 1) G).predict)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := 1) (k := 1) features
        (liftToABVisibleFamily (Z := Unit) (k := 1) G)) :
    False :=
  not_invariant_and_sharedSparseThreshold_of_surjective_lift_of_lt_cardFormula
    (Z := Unit) (r := 1) (k := 1) (Index := Index) (by decide) hinv hsurj hreal

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Unit 1 Index}
    {features : Fin 1 → AffineColumnCode (1 + 1)}
    (hinv : ABVisibleInvariant (Z := Unit) (k := 1) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Unit) (k := 1) G).predict)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := 1) (k := 1) features
        (liftToABVisibleFamily (Z := Unit) (k := 1) G)) :
    False :=
  not_invariant_and_sharedDecisionList_of_surjective_lift_of_lt_cardFormula
    (Z := Unit) (r := 1) (k := 1) (Index := Index) (by decide) hinv hsurj hreal

end Mettapedia.Computability.PNP.SharedABFeatureRouteCruxRegression
