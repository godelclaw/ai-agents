import Mettapedia.Computability.PNP.ABDecisionListObstruction

/-!
# PNP crux: the `(a,b)` decision-list route cannot keep full reduced expressivity

`ABDecisionListRoute.lean` packages the positive route surface:
if an exact family factors through the reduced raw visible view `(a,b)` and the
reduced family is realized by fixed-order decision lists, then the exact family
inherits the `2k+1` decision-list bit budget.

This file makes the matching contradiction explicit.  When the reduced
`(a,b)` family is still fully expressive, the same `2k+1` budget is below the
reduced truth-table threshold for every positive width `k`.  So the named
decision-list route assumptions are inconsistent on that route surface.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ} {Index : Type*}

/-- The factored `(a,b)` decision-list route is inconsistent whenever the
reduced family remains fully expressive on `ABVisibleSurface k`. -/
theorem not_factorsThrough_ab_and_decisionList_of_surjective_predict_of_pos
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hk : 0 < k)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    False := by
  have hsmall :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) :=
    exactVisibleCompressionTarget_of_factorsThrough_ab_and_decisionList_twoMul
      (Z := Z) (k := k) hfactor hreal
  have hle :
      Fintype.card (ABVisibleSurface k) ≤ 2 * k + 1 :=
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 * k + 1) hfactor hsurj hsmall
  have hlt : 2 * k + 1 < Fintype.card (ABVisibleSurface k) := by
    simpa [card_abVisibleSurface (k := k)] using
      abDecisionListBudget_lt_abTruthTable_of_pos (k := k) hk
  exact (Nat.not_le_of_lt hlt hle).elim

/-- Invariant-form contradiction: the lifted `(a,b)` decision-list route fails
whenever the reduced lift of the exact family is still fully expressive. -/
theorem not_invariant_and_decisionList_of_surjective_lift_of_pos
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hk : 0 < k)
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hsurj :
      Function.Surjective (liftToABVisibleFamily (Z := Z) (k := k) G).predict)
    (hreal :
      RealizedByABDecisionListFamily
        (k := k) (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    False := by
  exact
    not_factorsThrough_ab_and_decisionList_of_surjective_predict_of_pos
      (Z := Z) (k := k) hk
      (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
      hsurj hreal

/-- Concrete route-facing corollary: the full exact pullback of all raw
`(a,b)` rules cannot satisfy the decision-list route budget at positive width. -/
theorem fullExactABRuleFamily_not_exactVisibleCompressionTarget_of_pos
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ABVisibleSurface k → Bool)
        (fullExactABRuleFamily Z k) (2 * k + 1) := by
  exact
    not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k) (s := 2 * k + 1)
      (by simpa [card_abVisibleSurface (k := k)] using
        abDecisionListBudget_lt_abTruthTable_of_pos (k := k) hk)
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

end

end Mettapedia.Computability.PNP
