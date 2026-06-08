import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstruction

/-!
# Regression checks for the live injective exact-ZAB branch

These checks keep the non-collision lower bounds attached to the named exact
and shared exact ERM route surfaces.
-/

namespace Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionRegression

theorem exactZABDecisionListERMFamily_small_extractor_regression
    (zfeat : BitVec 2 → BitVec 2)
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 0) Bool) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec 2) (r := 2) (k := 0) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
      (n := 2) (r := 2) (k := 0) (Index := Unit)
      zfeat samples (by norm_num)

theorem sharedExactZABAffineFeatureERMFamily_small_feature_count_regression
    (zfeat : BitVec 2 → BitVec 2)
    {features : Fin 1 → AffineColumnCode (2 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec 2) (p := 1) (r := 2) (k := 0) zfeat features samples).predict := by
  exact
    sharedExactZABAffineFeatureERMFamily_not_surjective_of_featureCount_lt_visibleWidth
      (n := 2) (p := 1) (r := 2) (k := 0) (Index := Unit)
      zfeat features samples (by norm_num)

theorem sharedExactZABAffineDecisionListERMFamily_small_combiner_regression
    (zfeat : BitVec 2 → BitVec 2)
    {features : Fin 2 → AffineColumnCode (2 + (0 + 0))}
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 0) Bool) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec 2) (p := 2) (r := 2) (k := 0) zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_combinerWidth_lt_truthTableGap
      (n := 2) (p := 2) (r := 2) (k := 0) (Index := Unit)
      zfeat features samples (by norm_num)

end Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstructionRegression
