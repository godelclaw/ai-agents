import Mettapedia.Computability.PNP.ConditioningObstruction

/-!
# Regression checks for conditioning obstructions

These wrappers pin the finite-count countermodels used by the PNP v11 crux
audit: conditioning can collapse a uniform label map, and it can also destroy
independence between coordinates.
-/

namespace Mettapedia.Computability.PNP.ConditioningObstructionRegression

open Mettapedia.Computability.PNP

theorem conditioned_label_fiber_target_average_regression
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {d : Nat} (hd : 0 < d) (b : Label) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 1 := by
  exact conditioned_target_indicator_average_eq_one hd b

theorem conditioned_label_fiber_other_average_regression
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {d : Nat} {b c : Label} (hbc : c ≠ b) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 0 := by
  exact conditioned_other_indicator_average_eq_zero hbc

theorem bool_pair_unconditioned_independence_regression :
    CountIndependent (Ω := ConditioningBoolPair)
      conditioningFirstTrue conditioningSecondTrue := by
  exact conditioningBoolPair_unconditioned_first_second_independent

theorem bool_pair_diagonal_conditioning_destroys_independence_regression :
    ¬ CountIndependentWithin (Ω := ConditioningBoolPair)
      conditioningDiagonal conditioningFirstTrue conditioningSecondTrue := by
  exact not_conditioningBoolPair_conditioned_on_diagonal_first_second_independent

theorem coupled_nonconstant_conditioning_blocks_independence_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  exact
    not_countIndependentWithin_of_coupled_nonconstant_on_condition
      C E F hcouple hpos hneg

theorem coupled_conditioning_independence_iff_degenerate_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_coupled_iff_degenerate_on_condition
      C E F hcouple

theorem anticoupled_nonconstant_conditioning_blocks_independence_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  exact
    not_countIndependentWithin_of_anticoupled_nonconstant_on_condition
      C E F hanti hpos hneg

theorem anticoupled_conditioning_independence_iff_degenerate_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_anticoupled_iff_degenerate_on_condition
      C E F hanti

theorem bool_recoding_conditioning_independence_iff_degenerate_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_boolRecoding_iff_degenerate_on_condition
      C E F r hrec hnonconstant

theorem bool_recoding_constant_conditioning_independent_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hconstant : r true = r false) :
    CountIndependentWithin (Ω := Ω) C E F := by
  exact
    countIndependentWithin_of_boolRecoding_constant_on_condition
      C E F r hrec hconstant

theorem bool_recoding_conditioning_independence_iff_constant_or_degenerate_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_boolRecoding_iff_constant_or_degenerate_on_condition
      C E F r hrec

theorem bool_recoding_nonconstant_conditioning_blocks_independence_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  exact
    not_countIndependentWithin_of_boolRecoding_nonconstant_on_condition
      C E F r hrec hnonconstant hpos hneg

theorem bool_recoding_independent_nonconstant_source_is_constant_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hind : CountIndependentWithin (Ω := Ω) C E F)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  exact
    boolRecoding_constant_of_countIndependentWithin_of_nonconstant_on_condition
      C E F r hrec hind hpos hneg

theorem bool_recoding_nonconstant_source_independent_iff_constant_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔ r true = r false := by
  exact
    countIndependentWithin_boolRecoding_iff_constant_of_nonconstant_on_condition
      C E F r hrec hpos hneg

theorem bool_to_any_recoding_true_fiber_independence_iff_constant_or_degenerate_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
      C E r

theorem bool_to_any_recoding_true_fiber_nonconstant_blocks_independence_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true) := by
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_trueFiber_nonconstant_on_condition
      C E r hnonconstant hpos hneg

theorem bool_to_any_recoding_true_fiber_independent_nonconstant_source_is_constant_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  exact
    boolToAnyRecoding_trueFiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
      C E r hind hpos hneg

theorem bool_to_any_recoding_true_fiber_nonconstant_source_independent_iff_constant_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false := by
  exact
    countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_of_nonconstant_on_condition
      C E r hpos hneg

theorem bool_to_any_recoding_fiber_independence_iff_fiber_constant_or_degenerate_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  exact
    countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
      C E r y

theorem bool_to_any_recoding_fiber_distinguishes_blocks_independence_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) := by
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_fiber_distinguishes_on_condition
      C E r y hdistinguish hpos hneg

theorem bool_to_any_recoding_fiber_independent_nonconstant_source_is_fiber_constant_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    (r true = y ↔ r false = y) := by
  exact
    boolToAnyRecoding_fiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
      C E r y hind hpos hneg

theorem bool_to_any_recoding_fiber_nonconstant_source_independent_iff_fiber_constant_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) := by
  exact
    countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_of_nonconstant_on_condition
      C E r y hpos hneg

end Mettapedia.Computability.PNP.ConditioningObstructionRegression
