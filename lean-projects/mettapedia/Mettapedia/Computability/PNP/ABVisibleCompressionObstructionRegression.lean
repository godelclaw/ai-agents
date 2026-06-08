import Mettapedia.Computability.PNP.ABVisibleCompressionObstruction

/-!
# Regression checks for the raw `(a, b)` compression obstruction

These wrappers pin the reduced-surface blocker: once an exact switched family
factors through `(a, b)`, low-bit exact or clocked realization is still
impossible unless the reduced `(a, b)` family itself lands in a strict
subclass.
-/

namespace Mettapedia.Computability.PNP.ABVisibleCompressionObstructionRegression

open Mettapedia.Computability.PNP

section FullABRules

variable {k : ℕ}

def fullABRuleFamily (k : ℕ) :
    ABVisibleSwitchedFamily k (ABVisibleSurface k → Bool) where
  predict f := f

theorem fullABRuleFamily_surjective (k : ℕ) :
    Function.Surjective (fullABRuleFamily (k := k)).predict := by
  intro rule
  exact ⟨rule, rfl⟩

def fullExactABRuleFamily (Z : Type*) (k : ℕ) :
    ExactVisibleSwitchedFamily Z k (ABVisibleSurface k → Bool) where
  predict f u := f (abVisibleData u)

theorem fullExactABRuleFamily_factorsThrough_ab (Z : Type*) (k : ℕ) :
    (fullExactABRuleFamily Z k).FactorsThrough abVisibleData (fullABRuleFamily (k := k)) := by
  intro f u
  rfl

end FullABRules

theorem abVisibleHasBitBudget_of_exactVisibleCompressionTarget_of_factorsThrough_regression
    {Z : Type*} [Inhabited Z] {k s : ℕ} :
    let G := fullExactABRuleFamily Z k
    let H := fullABRuleFamily (k := k)
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := ABVisibleSurface k → Bool) G s →
      H.HasBitBudget s := by
  intro G H hsmall
  exact
    abVisibleHasBitBudget_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := s)
      (fullExactABRuleFamily_factorsThrough_ab Z k) hsmall

theorem fullExactABRuleFamily_not_exactVisibleCompressionTarget_regression :
    ¬ ExactVisibleCompressionTarget
        (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
        (fullExactABRuleFamily Unit 1) 3 := by
  exact
    not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Unit) (k := 1) (s := 3)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem fullExactABRuleFamily_not_finitePredictorCover_regression :
    ¬ (fullExactABRuleFamily Unit 1).FinitePredictorCover 15 := by
  exact
    not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem ab_visible_finitePredictorCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hcover

theorem ab_visible_not_finitePredictorCover_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FinitePredictorCover N := by
  exact
    not_finitePredictorCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hN hfactor

theorem ab_visible_not_exactVisibleCompressionTarget_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

theorem fullExactABRuleFamily_not_finiteIndexRepresentativeCover_regression :
    ¬ (fullExactABRuleFamily Unit 1).FiniteIndexRepresentativeCover 15 := by
  exact
    not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
      (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem ab_visible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hrep

theorem ab_visible_not_finiteIndexRepresentativeCover_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hN hfactor

theorem fullExactABRuleFamily_not_finitePredictorQuotient_regression :
    ¬ (fullExactABRuleFamily Unit 1).FinitePredictorQuotient 15 := by
  exact
    not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem ab_visible_finitePredictorQuotient_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hquot

theorem ab_visible_not_finitePredictorQuotient_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    not_finitePredictorQuotient_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hN hfactor

theorem fullExactABRuleFamily_not_invariantCompressionTarget_regression :
    ¬ InvariantCompressionTarget
        (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
        (fullExactABRuleFamily Unit 1) 3 := by
  exact
    not_invariantCompressionTarget_of_factorsThrough_ab_and_surjective_predict
      (Z := Unit) (k := 1) (s := 3)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem fullExactABRuleFamily_not_forkCompressionTarget_regression :
    ¬ ForkCompressionTarget
        (Z := Unit) (k := 1) (Index := ABVisibleSurface 1 → Bool)
        (fullExactABRuleFamily Unit 1) 3 := by
  exact
    not_forkCompressionTarget_of_factorsThrough_ab_and_surjective_predict
      (Z := Unit) (k := 1) (s := 3)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem fullExactABRuleFamily_not_exists_clockedRealization_regression :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Unit 1) 3 0,
        (fullExactABRuleFamily Unit 1).RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
      (Z := Unit) (k := 1) (s := 3) (clock := 0)
      (Index := ABVisibleSurface 1 → Bool)
      (by decide)
      (fullExactABRuleFamily_factorsThrough_ab Unit 1)
      (fullABRuleFamily_surjective 1)

theorem ab_visible_not_exists_clockedRealization_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

end Mettapedia.Computability.PNP.ABVisibleCompressionObstructionRegression
