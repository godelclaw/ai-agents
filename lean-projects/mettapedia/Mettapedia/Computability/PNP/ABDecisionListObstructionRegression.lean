import Mettapedia.Computability.PNP.ABDecisionListObstruction

/-!
# Regression checks for the raw `(a,b)` decision-list obstruction

These wrappers pin the strict-subclass result: the fixed-order `2k+1` raw
decision-list route cannot realize the full Boolean rule family on `(a,b)` once
`k > 0`, and the same obstruction lifts to the exact visible surface.
-/

namespace Mettapedia.Computability.PNP.ABDecisionListObstructionRegression

open Mettapedia.Computability.PNP

theorem abDecisionListBudget_lt_abTruthTable_k1_regression :
    2 * 1 + 1 < 2 ^ (2 * 1) := by
  exact abDecisionListBudget_lt_abTruthTable_of_pos (k := 1) (by decide)

theorem fullABRuleFamily_not_realizedByABDecisionListFamily_k1_regression :
    ¬ RealizedByABDecisionListFamily (k := 1) (fullABRuleFamily 1) := by
  exact fullABRuleFamily_not_realizedByABDecisionListFamily_of_pos (k := 1) (by decide)

theorem fullABRuleFamily_has_no_three_bit_budget_from_decision_lists_regression :
    ¬ RealizedByABDecisionListFamily (k := 1) (fullABRuleFamily 1) := by
  exact
    not_realizedByABDecisionListFamily_of_surjective_predict_of_lt_cardFormula
      (k := 1)
      (by decide)
      (fullABRuleFamily_surjective 1)

theorem fullExactABRuleFamily_not_realizedByRawExactABDecisionListFamily_k1_regression :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Unit) (k := 1)
        (fullExactABRuleFamily Unit 1) := by
  exact
    fullExactABRuleFamily_not_realizedByRawExactABDecisionListFamily_of_pos
      (Z := Unit) (k := 1) (by decide)

theorem factored_fullAB_not_realizedByRawExactABDecisionListFamily_k1_regression :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Unit) (k := 1)
        (fullExactABRuleFamily Unit 1) := by
  exact
    not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Unit) (k := 1)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

end Mettapedia.Computability.PNP.ABDecisionListObstructionRegression
