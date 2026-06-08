import Mettapedia.Computability.PNP.SharedABFeatureRoutes

/-!
# Regression checks for reduced raw `(a, b)` shared-feature obstructions

These wrappers pin the reduced-surface counting barrier directly on the shared
raw `(a, b)` route classes.
-/

namespace Mettapedia.Computability.PNP.SharedABFeatureRoutesRegression

open Mettapedia.Computability.PNP

def fullABRuleFamily (k : ℕ) :
    ABVisibleSwitchedFamily k (ABVisibleSurface k → Bool) where
  predict f := f

theorem fullABRuleFamily_surjective (k : ℕ) :
    Function.Surjective (fullABRuleFamily (k := k)).predict := by
  intro rule
  exact ⟨rule, rfl⟩

theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := 1) (k := 1) features (fullABRuleFamily (k := 1)) := by
  exact
    not_realizedBySharedABAffineFeatureFamily_of_surjective_predict_of_lt_surfaceCard
      (r := 1) (k := 1)
      (by simp [card_abVisibleSurface (k := 1)])
      (fullABRuleFamily_surjective 1)

theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := 1) (k := 1) features
        (fullABRuleFamily (k := 1)) := by
  exact
    not_realizedBySharedABSparseThresholdAffineFamily_of_surjective_predict_of_lt_surfaceCard
      (r := 1) (k := 1)
      (by simp [card_abVisibleSurface (k := 1)])
      (fullABRuleFamily_surjective 1)

theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_regression
    (features : Fin 2 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := 2) (k := 1) features
        (fullABRuleFamily (k := 1)) := by
  exact
    not_realizedBySharedABAffineDecisionListFamily_of_surjective_predict_of_lt_surfaceCard
      (r := 2) (k := 1)
      (by simp [card_abVisibleSurface (k := 1)])
      (fullABRuleFamily_surjective 1)

end Mettapedia.Computability.PNP.SharedABFeatureRoutesRegression
