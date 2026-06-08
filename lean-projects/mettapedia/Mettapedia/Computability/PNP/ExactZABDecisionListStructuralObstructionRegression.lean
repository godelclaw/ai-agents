import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstruction

namespace Mettapedia.Computability.PNP

abbrev zeroExtractor1 : BitVec 1 → BitVec 0 := fun _ => zeroVec

abbrev headExtractor1 : BitVec 1 → BitVec 1 := fun z => z

theorem full_rule_not_raw_exact_zab_decision_list_zero_extractor_regression :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec 1) (r := 0) (k := 1) zeroExtractor1
        (fullExactVisibleRuleFamily (BitVec 1) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_pos_widths
      (n := 1) (r := 0) (k := 1) zeroExtractor1 (by decide) (by decide)

theorem full_rule_not_raw_exact_zab_decision_list_head_extractor_regression :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec 1) (r := 1) (k := 1) headExtractor1
        (fullExactVisibleRuleFamily (BitVec 1) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_pos_widths
      (n := 1) (r := 1) (k := 1) headExtractor1 (by decide) (by decide)

theorem full_rule_actual_local_not_zab_decision_list_data_pos_widths_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1) headExtractor1) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_pos_widths
      (n := 1) (r := 1) (k := 1) headExtractor1 (by decide) (by decide)

end Mettapedia.Computability.PNP
