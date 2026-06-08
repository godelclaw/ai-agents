import Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstruction
import Mathlib.Tactic

/-!
# Regression checks for actual-local exact ZAB width obstructions
-/

namespace Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstructionRegression

theorem fullRuleActualLocal_zabData_forces_three_extractor_bits_regression
    {r : ℕ}
    {zfeat : BitVec 2 → BitVec r}
    (h :
      ActualSwitchedLocalInterface.ZABDecisionListData
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0) zfeat) :
    3 ≤ r := by
  exact
    h.extractorWidthLowerBound_of_surjective_predict
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)

theorem fullRuleActualLocal_not_zabData_below_truthTableGap_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          (fun z : BitVec 2 => z)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_extractorWidth_lt_truthTableGap
      (n := 2) (k := 0) (r := 2) (fun z : BitVec 2 => z) (by norm_num)

end Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstructionRegression
