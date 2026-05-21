import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundation

/-!
# Regression checks for finite-coin postprocessing foundations

These wrappers pin exact erasure preservation and the finite-preimage blowup
bound for approximate finite-coin source/output independence.
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression

open Mettapedia.Computability.PNP

theorem finite_output_map_fiber_card_bound_card_regression
    {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) :
    finiteOutputMapFiberCardBound g (Fintype.card α) := by
  exact finiteOutputMapFiberCardBound_card g

theorem predicate_neutral_postcompose_regression
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (P : β → Prop) [DecidablePred P]
    (hneutral : finiteCoinOutputPredicateNeutral r (fun y => P (g y))) :
    finiteCoinOutputPredicateNeutral (fun b c => g (r b c)) P := by
  exact finiteCoinOutputPredicateNeutral_postcompose r g P hneutral

theorem predicate_erasing_postcompose_regression
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) := by
  exact finiteCoinOutputPredicateErasing_postcompose r g herase

theorem fiber_balanced_postcompose_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinRecodingFiberBalanced_postcompose r g hbal

theorem true_fiber_count_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_injective r g hinj y

theorem false_fiber_count_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_injective r g hinj y

theorem fiber_balanced_of_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj hbal

theorem fiber_balanced_postcompose_iff_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective r g hinj

theorem predicate_erasing_postcompose_iff_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_injective r g hinj

theorem fiber_balanced_of_postcompose_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
    r g recover hrecover hbal

theorem fiber_balanced_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

theorem predicate_erasing_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

theorem fiber_balanced_of_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    r g hinjObs hbal

theorem fiber_balanced_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    r g hinjObs

theorem observed_output_collision_of_postcompose_balanced_not_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact
    exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
      r g hbal hnot

theorem predicate_erasing_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_observedInjective
    r g hinjObs

theorem false_heavy_collision_of_true_heavy_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yTrue : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue) :
    ∃ yFalse : α,
      g yFalse = g yTrue ∧ yFalse ≠ yTrue ∧
        coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
    r g hbal hheavy

theorem true_heavy_collision_of_false_heavy_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yFalse : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse) :
    ∃ yTrue : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue := by
  exact exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
    r g hbal hheavy

theorem opposite_bias_collision_of_postcompose_balanced_not_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

theorem fiber_balanced_constant_regression
    {Coin β : Type*} [Fintype Coin] [DecidableEq β] (z : β) :
    FiniteCoinRecodingFiberBalanced (fun _b (_c : Coin) => z) := by
  exact finiteCoinRecodingFiberBalanced_constant z

theorem true_fiber_count_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinTrueFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_eq_sum_preimage r g z

theorem false_fiber_count_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinFalseFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_eq_sum_preimage r g z

theorem signed_fiber_bias_postcompose_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinSignedFiberBias (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
  exact finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z

theorem fiber_balanced_iff_signed_bias_zero_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinSignedFiberBias r y = 0 := by
  exact finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero r

theorem signed_fiber_bias_sum_preimage_zero_of_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) (z : β) :
    (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) = 0 := by
  exact finiteCoinSignedFiberBias_sum_preimage_eq_zero_of_postcompose_fiberBalanced
    r g hbal z

theorem fiber_balanced_postcompose_iff_signed_bias_sum_preimage_zero_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  exact
    finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
      r g

theorem fiber_imbalance_postcompose_le_sum_preimage_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z ≤
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  exact finiteCoinFiberImbalance_postcompose_le_sum_preimage r g z

theorem output_tolerance_postcompose_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g hbound happrox

theorem output_tolerance_postcompose_card_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (Fintype.card α * τ) := by
  exact countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_card
    r g happrox

theorem output_defect_postcompose_le_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m : Nat}
    (hbound : finiteOutputMapFiberCardBound g m) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    m *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    r g hbound

theorem output_defect_postcompose_le_card_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    Fintype.card α *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le_card
    r g

theorem true_fiber_count_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_observedInjective r g hinjObs hobs

theorem false_fiber_count_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_observedInjective r g hinjObs hobs

theorem output_tolerance_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      r g τ hinjObs

theorem output_tolerance_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α) (τ : Nat)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedLeftInverse
      r g recover τ hrecover

theorem output_defect_postcompose_eq_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
    r g hinjObs

theorem output_defect_postcompose_eq_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  exact countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
    r g recover hrecover

def boolPairObservedSupportRecoding : Bool → Unit → Bool × Bool
  | true, () => (true, false)
  | false, () => (false, false)

def boolPairFirstProjection : Bool × Bool → Bool :=
  fun p => p.1

def boolPairObservedSupportRecover : Bool → Bool × Bool :=
  fun b => (b, false)

theorem boolPairFirstProjection_not_injective_regression :
    ¬ Function.Injective boolPairFirstProjection := by
  intro hinj
  have hEq :
      ((false, false) : Bool × Bool) = (false, true) := by
    apply hinj
    rfl
  have hNeq : ((false, false) : Bool × Bool) ≠ (false, true) := by
    decide
  exact hNeq hEq

theorem boolPairObservedSupportRecoding_firstProjection_observed_injective_regression :
    ∀ b1 c1 b2 c2,
      boolPairFirstProjection (boolPairObservedSupportRecoding b1 c1) =
        boolPairFirstProjection (boolPairObservedSupportRecoding b2 c2) →
      boolPairObservedSupportRecoding b1 c1 =
        boolPairObservedSupportRecoding b2 c2 := by
  intro b1 c1 b2 c2 hEq
  cases b1 <;> cases c1 <;> cases b2 <;> cases c2 <;>
    simp [boolPairObservedSupportRecoding, boolPairFirstProjection] at hEq ⊢

theorem boolPairObservedSupportRecoding_firstProjection_left_inverse_regression :
    ∀ b c,
      boolPairObservedSupportRecover
          (boolPairFirstProjection (boolPairObservedSupportRecoding b c)) =
        boolPairObservedSupportRecoding b c := by
  intro b c
  cases b <;> cases c <;>
    rfl

theorem output_tolerance_postcompose_iff_observed_injective_not_global_injective_regression
    (τ : Nat) :
    ¬ Function.Injective boolPairFirstProjection ∧
      (CountIndependentWithinToleranceOutput (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput
          (fun b c => boolPairFirstProjection (boolPairObservedSupportRecoding b c))) τ ↔
      CountIndependentWithinToleranceOutput (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput boolPairObservedSupportRecoding) τ) := by
  refine ⟨boolPairFirstProjection_not_injective_regression, ?_⟩
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      boolPairObservedSupportRecoding boolPairFirstProjection τ
      boolPairObservedSupportRecoding_firstProjection_observed_injective_regression

theorem output_defect_postcompose_eq_observed_left_inverse_not_global_injective_regression :
    ¬ Function.Injective boolPairFirstProjection ∧
      countIndependentWithinOutputDefect (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput
          (fun b c => boolPairFirstProjection (boolPairObservedSupportRecoding b c))) =
      countIndependentWithinOutputDefect (Ω := Bool × Unit)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Unit))
        (finiteCoinOutput boolPairObservedSupportRecoding) := by
  refine ⟨boolPairFirstProjection_not_injective_regression, ?_⟩
  exact
    countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
      boolPairObservedSupportRecoding
      boolPairFirstProjection
      boolPairObservedSupportRecover
      boolPairObservedSupportRecoding_firstProjection_left_inverse_regression

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression
