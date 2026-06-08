import Mettapedia.Computability.PNP.ABDecisionListRouteCrux

/-!
# Regression checks for the `(a,b)` decision-list route crux

These wrappers keep the route-facing contradiction surface small and reusable.
-/

namespace Mettapedia.Computability.PNP.ABDecisionListRouteCruxRegression

open Mettapedia.Computability.PNP

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Unit 1 Index}
    (hinv : ABVisibleInvariant (Z := Unit) (k := 1) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Unit) (k := 1) G).predict)
    (hreal :
      RealizedByABDecisionListFamily
        (k := 1) (liftToABVisibleFamily (Z := Unit) (k := 1) G)) :
    False :=
  not_invariant_and_decisionList_of_surjective_lift_of_pos
    (Z := Unit) (k := 1) (Index := Index) (by decide) hinv hsurj hreal

example :
    ¬ ExactVisibleCompressionTarget
        (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
        (fullExactABRuleFamily Unit 1) 3 :=
  fullExactABRuleFamily_not_exactVisibleCompressionTarget_of_pos
    Unit (k := 1) (by decide)

end Mettapedia.Computability.PNP.ABDecisionListRouteCruxRegression
