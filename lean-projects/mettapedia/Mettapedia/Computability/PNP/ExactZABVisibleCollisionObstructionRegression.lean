import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstruction

/-!
# Regression checks for exact-ZAB visible-summary collision obstructions

These wrappers keep the noninjective-extractor blocker attached to the broader
exact/shared exact `(zfeat(z), a, b)` route surfaces, not only the raw
decision-list route.
-/

namespace Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionRegression

def zeroExtractor : Bool → BitVec 0 := fun _ i => Fin.elim0 i

theorem zeroExtractor_not_injective :
    ¬ Function.Injective zeroExtractor := by
  intro hinj
  have h : true = false := hinj (by
    funext i
    exact Fin.elim0 i)
  cases h

theorem exactZABAffineFeatureERMFamily_zeroExtractor_regression
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := Bool) (p := 1) (r := 0) (k := 0) zeroExtractor samples).predict := by
  exact
    exactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Bool) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor samples zeroExtractor_not_injective

theorem exactZABSparseThresholdAffineERMFamily_zeroExtractor_regression
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := Bool) (p := 1) (r := 0) (k := 0) zeroExtractor samples).predict := by
  exact
    exactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Bool) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor samples zeroExtractor_not_injective

theorem sharedExactZABAffineFeatureERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Bool) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Bool) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples zeroExtractor_not_injective

theorem sharedExactZABSparseThresholdAffineERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Bool) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Bool) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples zeroExtractor_not_injective

theorem sharedExactZABAffineDecisionListERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := Bool) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Bool) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples zeroExtractor_not_injective

end Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionRegression
