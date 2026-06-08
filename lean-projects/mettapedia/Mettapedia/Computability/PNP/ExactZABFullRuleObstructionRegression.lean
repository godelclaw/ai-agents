import Mettapedia.Computability.PNP.ExactZABFullRuleObstruction
import Mathlib.Tactic

/-!
# Regression checks for exact-ZAB full-rule obstructions
-/

namespace Mettapedia.Computability.PNP.ExactZABFullRuleObstructionRegression

theorem full_rule_not_raw_exact_zab_decision_list_small_widened_regression
    (zfeat : BitVec 2 → BitVec 3) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec 2) (r := 3) (k := 1)
        zfeat (fullExactVisibleRuleFamily (BitVec 2) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_extractorWidth_lt_truthTableGap
      (n := 2) (r := 3) (k := 1) zfeat (by norm_num)

theorem full_rule_not_shared_exact_zab_affine_feature_small_regression
    (zfeat : BitVec 2 → BitVec 3)
    (features : Fin 3 → AffineColumnCode (3 + (1 + 1))) :
    ¬ RealizedBySharedExactZABAffineFeatureFamily
        (Z := BitVec 2) (p := 3) (r := 3) (k := 1)
        zfeat features (fullExactVisibleRuleFamily (BitVec 2) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineFeatureFamily_of_featureCount_lt_visibleWidth
      (n := 2) (p := 3) (r := 3) (k := 1) zfeat features (by norm_num)

theorem full_rule_not_shared_exact_zab_sparse_threshold_small_regression
    (zfeat : BitVec 2 → BitVec 3)
    (features : Fin 7 → AffineColumnCode (3 + (1 + 1))) :
    ¬ RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := BitVec 2) (p := 7) (r := 3) (k := 1)
        zfeat features (fullExactVisibleRuleFamily (BitVec 2) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABSparseThresholdAffineFamily_of_linearBudget_lt_surfaceCard
      (n := 2) (p := 7) (r := 3) (k := 1) zfeat features (by norm_num)

theorem full_rule_not_shared_exact_zab_decision_list_small_regression
    (zfeat : BitVec 2 → BitVec 3)
    (features : Fin 4 → AffineColumnCode (3 + (1 + 1))) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := BitVec 2) (p := 4) (r := 3) (k := 1)
        zfeat features (fullExactVisibleRuleFamily (BitVec 2) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_combinerWidth_lt_truthTableGap
      (n := 2) (p := 4) (r := 3) (k := 1) zfeat features (by norm_num)

end Mettapedia.Computability.PNP.ExactZABFullRuleObstructionRegression
