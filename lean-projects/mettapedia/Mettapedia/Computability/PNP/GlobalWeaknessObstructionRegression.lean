import Mettapedia.Computability.PNP.GlobalWeaknessObstruction

/-!
# Regression checks for global weakness obstructions

The checks pin the distinction between a scalar weakness summary and a genuine
encoded family of classifiers.  If every selected predictor is decoded only from
one global weakness value, the family cannot realize all Boolean classifiers on
any nontrivial state space.
-/

namespace Mettapedia.Computability.PNP.GlobalWeaknessObstructionRegression

open Mettapedia.Computability.PNP
open Mettapedia.GSLT.Meredith.WeaknessBridge

universe u v

variable {U : Type u} [Fintype U] [DecidableEq U]
variable {Q : Type v} [Monoid Q] [CompleteLattice Q]

theorem distinction_family_cannot_select_separating_target_regression
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict)
    {target : U → Bool} {u v : U}
    (hsep : target u ≠ target v) :
    ¬ ∃ i : Index, predict i = target := by
  exact
    not_exists_eq_of_familyFactorsThroughDistinctionWeakness_of_separates
      ev hfamily hsep

theorem nonDistinction_family_cannot_select_separating_target_regression
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict)
    {target : U → Bool} {u v : U}
    (hsep : target u ≠ target v) :
    ¬ ∃ i : Index, predict i = target := by
  exact
    not_exists_eq_of_familyFactorsThroughNonDistinctionWeakness_of_separates
      ev hfamily hsep

theorem distinction_family_not_surjective_on_nontrivial_states_regression
    [Nontrivial U]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    not_surjective_familyFactorsThroughDistinctionWeakness_of_nontrivial
      ev hfamily

theorem nonDistinction_family_not_surjective_on_nontrivial_states_regression
    [Nontrivial U]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    not_surjective_familyFactorsThroughNonDistinctionWeakness_of_nontrivial
      ev hfamily

end Mettapedia.Computability.PNP.GlobalWeaknessObstructionRegression
