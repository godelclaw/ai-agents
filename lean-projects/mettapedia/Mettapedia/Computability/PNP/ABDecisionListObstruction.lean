import Mettapedia.Computability.PNP.ABVisibleCompressionObstruction
import Mathlib.Tactic

/-!
# PNP crux: raw `(a, b)` decision lists are a strict repair subclass

The positive raw `(a,b)` route says that a family realized by the fixed-order
decision-list decoder has an exact bit budget `2k+1`.  This file records the
matching negative foundation: for `k > 0`, that budget is strictly below the
truth-table budget for all Boolean rules on `(a,b)`.

Consequently, a repair that routes the exact switched family through the raw
`(a,b)` decision-list class must prove a genuine strict-subclass theorem for
the actual switched predictors.  It cannot cover a family that is still fully
expressive on the reduced raw surface.
-/

namespace Mettapedia.Computability.PNP

section RawABDecisionList

variable {k : ℕ}

/-- The fixed-order decision-list decoder directly on the reduced raw
`(a,b)` surface. -/
noncomputable def abDecisionListBitFamily (k : ℕ) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (k + k + 1) where
  decode raw x :=
    let code := (sharedAffineDecisionListCodeEquivBitCode (k + k)).symm raw
    abDecisionListPredict (k := k) code x

@[simp] theorem abDecisionListBitFamily_decode_code
    (code : SharedAffineDecisionListCode (k + k)) :
    (abDecisionListBitFamily k).decode
        (sharedAffineDecisionListCodeEquivBitCode (k + k) code)
      = abDecisionListPredict (k := k) code := by
  funext x
  simp [abDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

/-- Realization by the raw `(a,b)` decision-list class supplies the corresponding
`k+k+1` bit budget on the reduced raw surface itself. -/
theorem abVisibleHasBitBudget_of_realizedByABDecisionListFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    H.HasBitBudget (k + k + 1) := by
  refine ⟨abDecisionListBitFamily k, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode (k + k) code, ?_⟩
  exact (abDecisionListBitFamily_decode_code (k := k) code).trans hi.symm

/-- Two-multiplication form of the raw `(a,b)` decision-list bit budget. -/
theorem abVisibleHasBitBudget_of_realizedByABDecisionListFamily_twoMul
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    H.HasBitBudget (2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    abVisibleHasBitBudget_of_realizedByABDecisionListFamily (k := k) hreal

/-- The fixed-order decision-list budget is strictly below the full truth-table
budget on `(a,b)` as soon as there is at least one visible bit in each block. -/
theorem abDecisionListBudget_lt_abTruthTable_of_pos
    (hk : 0 < k) :
    2 * k + 1 < 2 ^ (2 * k) := by
  have hwidth : 2 ≤ 2 * k := by omega
  have hmain : ∀ m : ℕ, m + 3 < 2 ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
        norm_num
    | succ m ih =>
        have hle : m + 4 ≤ 2 * (m + 3) := by omega
        have hlt : 2 * (m + 3) < 2 * 2 ^ (m + 2) := by
          exact Nat.mul_lt_mul_of_pos_left ih Nat.zero_lt_two
        exact lt_of_le_of_lt hle <| by
          simpa [Nat.pow_succ, Nat.add_assoc, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using hlt
  rcases Nat.exists_eq_add_of_le hwidth with ⟨m, hm⟩
  rw [hm]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain m

/-- If a reduced `(a,b)` family is fully expressive, any decision-list
realization of it would force the full truth-table lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedByABDecisionListFamily_of_surjective_predict
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * k + 1 := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := 2 * k + 1) hsurj
      (abVisibleHasBitBudget_of_realizedByABDecisionListFamily_twoMul
        (k := k) hreal)

/-- Therefore the raw `(a,b)` decision-list route cannot realize a reduced
family that is still all Boolean rules on `(a,b)` below the surface-cardinality
threshold. -/
theorem not_realizedByABDecisionListFamily_of_surjective_predict_of_budget_lt
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hbudget : 2 * k + 1 < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByABDecisionListFamily (k := k) H := by
  intro hreal
  exact Nat.not_le_of_lt hbudget <|
    abVisible_surfaceCard_le_of_realizedByABDecisionListFamily_of_surjective_predict
      (k := k) hsurj hreal

/-- Formula form of the same raw `(a,b)` decision-list obstruction. -/
theorem not_realizedByABDecisionListFamily_of_surjective_predict_of_lt_cardFormula
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hbudget : 2 * k + 1 < 2 ^ (2 * k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByABDecisionListFamily (k := k) H := by
  exact
    not_realizedByABDecisionListFamily_of_surjective_predict_of_budget_lt
      (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hbudget)
      hsurj

/-- Positive-width form: for every `k > 0`, full expressivity on `(a,b)` is
incompatible with the fixed-order `2k+1` decision-list route. -/
theorem not_realizedByABDecisionListFamily_of_surjective_predict_of_pos
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hk : 0 < k)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByABDecisionListFamily (k := k) H := by
  exact
    not_realizedByABDecisionListFamily_of_surjective_predict_of_lt_cardFormula
      (k := k) (abDecisionListBudget_lt_abTruthTable_of_pos (k := k) hk) hsurj

end RawABDecisionList

section ExactLift

variable {Z : Type*} {k : ℕ} {Index : Type*}

/-- If an exact family factors through `(a,b)` and the reduced family is fully
expressive, then a raw exact-surface decision-list realization would force the
same reduced truth-table lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * k + 1 := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 * k + 1) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedByRawExactABDecisionListFamily_twoMul
        (Z := Z) (k := k) (Index := Index) hreal)

/-- Lifted obstruction: a factored exact family whose reduced `(a,b)` family is
fully expressive cannot be realized by the raw exact decision-list class below
the reduced truth-table threshold. -/
theorem not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_budget_lt
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hbudget : 2 * k + 1 < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G := by
  intro hreal
  exact Nat.not_le_of_lt hbudget <|
    abVisible_surfaceCard_le_of_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (k := k) hfactor hsurj hreal

/-- Formula form of the lifted raw exact decision-list obstruction. -/
theorem not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hbudget : 2 * k + 1 < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G := by
  exact
    not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_budget_lt
      (Z := Z) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hbudget)
      hfactor hsurj

/-- Positive-width form of the lifted raw exact decision-list obstruction. -/
theorem not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_pos
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hk : 0 < k)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k) G := by
  exact
    not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Z) (k := k)
      (abDecisionListBudget_lt_abTruthTable_of_pos (k := k) hk)
      hfactor hsurj

end ExactLift

section FullRuleFamily

/-- The full Boolean rule family on the reduced raw `(a,b)` surface. -/
def fullABRuleFamily (k : ℕ) :
    ABVisibleSwitchedFamily k (ABVisibleSurface k → Bool) where
  predict rule := rule

theorem fullABRuleFamily_surjective (k : ℕ) :
    Function.Surjective (fullABRuleFamily k).predict := by
  intro rule
  exact ⟨rule, rfl⟩

/-- The pullback of the full raw `(a,b)` rule family to the exact visible
surface. -/
def fullExactABRuleFamily (Z : Type*) (k : ℕ) :
    ExactVisibleSwitchedFamily Z k (ABVisibleSurface k → Bool) where
  predict rule u := rule (abVisibleData u)

theorem fullExactABRuleFamily_factorsThrough_ab (Z : Type*) (k : ℕ) :
    (fullExactABRuleFamily Z k).FactorsThrough abVisibleData
      (fullABRuleFamily k) := by
  intro rule u
  rfl

/-- The full raw `(a,b)` rule family is not a fixed-order decision-list family
for any positive width. -/
theorem fullABRuleFamily_not_realizedByABDecisionListFamily_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByABDecisionListFamily (k := k) (fullABRuleFamily k) := by
  exact
    not_realizedByABDecisionListFamily_of_surjective_predict_of_pos
      (k := k) hk (fullABRuleFamily_surjective k)

/-- Its exact-surface pullback is likewise not realized by the raw exact
decision-list class for any positive width. -/
theorem fullExactABRuleFamily_not_realizedByRawExactABDecisionListFamily_of_pos
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k)
        (fullExactABRuleFamily Z k) := by
  exact
    not_realizedByRawExactABDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_pos
      (Z := Z) (k := k) hk
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

end FullRuleFamily

end Mettapedia.Computability.PNP
