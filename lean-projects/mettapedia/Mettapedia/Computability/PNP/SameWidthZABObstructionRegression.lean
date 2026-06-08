import Mettapedia.Computability.PNP.SameWidthZABObstruction

/-!
# Regression checks for the same-width exact ZAB obstruction
-/

namespace Mettapedia.Computability.PNP.SameWidthZABObstructionRegression

theorem exactZABDecisionListERMFamily_same_width_regression
    (zfeat : BitVec 2 → BitVec 2)
    (samples : Unit → Sample (ExactVisiblePostSwitchSurface (BitVec 2) 0) Bool) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec 2) (r := 2) (k := 0) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_sameWidth
      (n := 2) (k := 0) (Index := Unit) zfeat samples (by norm_num)

theorem fullRuleActualLocal_same_width_no_zabData_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          (fun z : BitVec 2 => z)) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_sameWidth
      (n := 2) (k := 0) (fun z : BitVec 2 => z) (by norm_num)

end Mettapedia.Computability.PNP.SameWidthZABObstructionRegression
