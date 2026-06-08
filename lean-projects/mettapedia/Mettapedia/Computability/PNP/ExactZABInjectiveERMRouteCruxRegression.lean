import Mettapedia.Computability.PNP.ExactZABInjectiveERMRouteCrux
import Mathlib.Tactic

/-!
# Regression checks for widened injective exact-ZAB ERM route contradictions
-/

namespace Mettapedia.Computability.PNP.ExactZABInjectiveERMRouteCruxRegression

theorem no_widened_small_exactZABERM_matches_full_rule_regression
    (zfeat : BitVec 2 → BitVec 3) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec 2) 1 →
          Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool,
        exactZABDecisionListERMFamily
            (Z := BitVec 2) (r := 3) (k := 1)
            (Index := ExactVisibleRule (BitVec 2) 1)
            zfeat samples =
          fullExactVisibleRuleFamily (BitVec 2) 1 := by
  exact
    not_exists_exactZABDecisionListERMFamily_eq_fullExactVisibleRuleFamily_of_extractorWidth_lt_truthTableGap
      (n := 2) (r := 3) (k := 1) zfeat (by norm_num)

theorem no_widened_small_sharedFeatureERM_matches_full_rule_regression
    (zfeat : BitVec 2 → BitVec 3)
    (features : Fin 3 → AffineColumnCode (3 + (1 + 1))) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec 2) 1 →
          Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool,
        sharedExactZABAffineFeatureERMFamily
            (Z := BitVec 2) (p := 3) (r := 3) (k := 1)
            (Index := ExactVisibleRule (BitVec 2) 1)
            zfeat features samples =
          fullExactVisibleRuleFamily (BitVec 2) 1 := by
  exact
    not_exists_sharedExactZABAffineFeatureERMFamily_eq_fullExactVisibleRuleFamily_of_featureCount_lt_visibleWidth
      (n := 2) (p := 3) (r := 3) (k := 1) zfeat features (by norm_num)

theorem no_widened_small_sharedDecisionListERM_matches_full_rule_regression
    (zfeat : BitVec 2 → BitVec 3)
    (features : Fin 4 → AffineColumnCode (3 + (1 + 1))) :
    ¬ ∃ samples :
        ExactVisibleRule (BitVec 2) 1 →
          Sample (ExactVisiblePostSwitchSurface (BitVec 2) 1) Bool,
        sharedExactZABAffineDecisionListERMFamily
            (Z := BitVec 2) (p := 4) (r := 3) (k := 1)
            (Index := ExactVisibleRule (BitVec 2) 1)
            zfeat features samples =
          fullExactVisibleRuleFamily (BitVec 2) 1 := by
  exact
    not_exists_sharedExactZABAffineDecisionListERMFamily_eq_fullExactVisibleRuleFamily_of_combinerWidth_lt_truthTableGap
      (n := 2) (p := 4) (r := 3) (k := 1) zfeat features (by norm_num)

end Mettapedia.Computability.PNP.ExactZABInjectiveERMRouteCruxRegression
