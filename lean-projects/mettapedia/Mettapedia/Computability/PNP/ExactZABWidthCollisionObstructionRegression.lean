import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstruction

/-!
# Regression checks for exact-ZAB width collision obstructions

These checks keep the width-compressing extractor blocker attached to the named
exact/shared exact ERM routes.
-/

namespace Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionRegression

def zeroExtractor : BitVec 1 → BitVec 0 := fun _ i => Fin.elim0 i

theorem exactZABDecisionListERMFamily_zeroExtractor_regression
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec 1) (r := 0) (k := 0) zeroExtractor samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_width_lt
      (n := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor samples (by decide)

theorem exactZABAffineFeatureERMFamily_zeroExtractor_regression
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := BitVec 1) (p := 1) (r := 0) (k := 0) zeroExtractor samples).predict := by
  exact
    exactZABAffineFeatureERMFamily_not_surjective_of_width_lt
      (n := 1) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor samples (by decide)

theorem exactZABSparseThresholdAffineERMFamily_zeroExtractor_regression
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := BitVec 1) (p := 1) (r := 0) (k := 0) zeroExtractor samples).predict := by
  exact
    exactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
      (n := 1) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor samples (by decide)

theorem sharedExactZABAffineFeatureERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec 1) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABAffineFeatureERMFamily_not_surjective_of_width_lt
      (n := 1) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples (by decide)

theorem sharedExactZABSparseThresholdAffineERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := BitVec 1) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
      (n := 1) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples (by decide)

theorem sharedExactZABAffineDecisionListERMFamily_zeroExtractor_regression
    {features : Fin 1 → AffineColumnCode (0 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 1) 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec 1) (p := 1) (r := 0) (k := 0) zeroExtractor features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_width_lt
      (n := 1) (p := 1) (r := 0) (k := 0) (Index := Unit)
      zeroExtractor features samples (by decide)

end Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionRegression
