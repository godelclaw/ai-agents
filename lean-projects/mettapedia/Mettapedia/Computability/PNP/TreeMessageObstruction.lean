import Mettapedia.Computability.PNP.ExactSwitchedFamily
import Mathlib.Tactic

/-!
# P vs NP crux: tree structure alone does not force a small message class

One natural rescue route is:

> "The local neighborhoods are tree-like, so the witness-bit rule should come
> from a tiny message-passing or dynamic-program class."

This file shows that tree structure by itself is far too weak.  Even a *fixed
perfect binary tree architecture* of depth `n` realizes every Boolean rule on
`n` visible bits, just by choosing the leaf labels appropriately.  So no exact
compression theorem can follow from tree-likeness alone.
-/

namespace Mettapedia.Computability.PNP

/-- Perfect binary decision trees of depth `n`, with only the leaves carrying
data. Internal nodes just branch on the next visible input bit. -/
inductive DecisionTree : ℕ → Type
  | leaf : Bool → DecisionTree 0
  | node : DecisionTree n → DecisionTree n → DecisionTree (n + 1)

/-- The unique width-`0` visible input. -/
def emptyBits : VisibleBits 0 := fun i => Fin.elim0 i

/-- Drop the first visible bit. -/
def tailBits {n : ℕ} (x : VisibleBits (n + 1)) : VisibleBits n :=
  fun i => x i.succ

/-- Prepend one visible bit. -/
def consBits {n : ℕ} (b : Bool) (x : VisibleBits n) : VisibleBits (n + 1) :=
  Fin.cases b x

lemma tailBits_consBits {n : ℕ} (b : Bool) (x : VisibleBits n) :
    tailBits (consBits b x) = x := by
  funext i
  simp [tailBits, consBits]

lemma consBits_head_tail {n : ℕ} (x : VisibleBits (n + 1)) :
    consBits (x 0) (tailBits x) = x := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [consBits]
  · intro j
    simp [consBits, tailBits]

/-- Evaluate a depth-`n` decision tree on `n` visible bits. -/
def DecisionTree.eval : {n : ℕ} → DecisionTree n → LocalRule n
  | 0, .leaf b => fun _ => b
  | _ + 1, .node left right => fun x =>
      if x 0 then DecisionTree.eval right (tailBits x) else DecisionTree.eval left (tailBits x)

/-- Encode any Boolean rule as a leaf-labeled perfect binary decision tree. -/
def encodeDecisionTree : {n : ℕ} → LocalRule n → DecisionTree n
  | 0, rule => .leaf (rule emptyBits)
  | _ + 1, rule =>
      .node
        (encodeDecisionTree fun x => rule (consBits false x))
        (encodeDecisionTree fun x => rule (consBits true x))

theorem eval_encodeDecisionTree : ∀ {n : ℕ} (rule : LocalRule n),
    DecisionTree.eval (encodeDecisionTree rule) = rule
  | 0, rule => by
      funext x
      have hx : x = emptyBits := by
        funext i
        exact Fin.elim0 i
      simp [encodeDecisionTree, DecisionTree.eval, hx]
  | n + 1, rule => by
      funext x
      by_cases hx : x 0
      · have ih :=
          congrFun (eval_encodeDecisionTree (rule := fun y => rule (consBits true y))) (tailBits x)
        have hcons : consBits true (tailBits x) = x := by
          simpa [hx] using consBits_head_tail x
        simpa [DecisionTree.eval, encodeDecisionTree, hx, hcons] using ih
      · have ih :=
          congrFun (eval_encodeDecisionTree (rule := fun y => rule (consBits false y))) (tailBits x)
        have hcons : consBits false (tailBits x) = x := by
          simpa [hx] using consBits_head_tail x
        simpa [DecisionTree.eval, encodeDecisionTree, hx, hcons] using ih

/-- In the fixed perfect-tree architecture, extensional equality of semantics
is equality of leaf labels. -/
theorem DecisionTree.eq_of_eval_eq :
    ∀ {n : ℕ} {left right : DecisionTree n},
      DecisionTree.eval left = DecisionTree.eval right → left = right
  | 0, .leaf b₁, .leaf b₂, h => by
      have hb : b₁ = b₂ := by
        simpa [DecisionTree.eval] using congrFun h emptyBits
      simp [hb]
  | n + 1, .node left₁ right₁, .node left₂ right₂, h => by
      have hleftEval : DecisionTree.eval left₁ = DecisionTree.eval left₂ := by
        funext x
        have hpoint := congrFun h (consBits false x)
        simpa [DecisionTree.eval, tailBits_consBits] using hpoint
      have hrightEval : DecisionTree.eval right₁ = DecisionTree.eval right₂ := by
        funext x
        have hpoint := congrFun h (consBits true x)
        simpa [DecisionTree.eval, tailBits_consBits] using hpoint
      have hleft : left₁ = left₂ :=
        DecisionTree.eq_of_eval_eq hleftEval
      have hright : right₁ = right₂ :=
        DecisionTree.eq_of_eval_eq hrightEval
      simp [hleft, hright]

/-- Evaluation is injective for the fixed perfect-tree architecture. -/
theorem evalDecisionTree_injective (n : ℕ) :
    Function.Injective (@DecisionTree.eval n) := by
  intro left right h
  exact DecisionTree.eq_of_eval_eq h

/-- The fixed-depth perfect-tree architecture realizes the full local-rule class. -/
theorem evalDecisionTree_surjective (n : ℕ) :
    Function.Surjective (@DecisionTree.eval n) := by
  intro rule
  exact ⟨encodeDecisionTree rule, eval_encodeDecisionTree rule⟩

/-- Evaluation is a bijection between fixed-depth perfect trees and local
Boolean rules. -/
theorem evalDecisionTree_bijective (n : ℕ) :
    Function.Bijective (@DecisionTree.eval n) :=
  ⟨evalDecisionTree_injective n, evalDecisionTree_surjective n⟩

/-- Equivalently, the semantics realized by depth-`n` decision trees is all of
`LocalRule n`. -/
theorem decisionTreeSemantics_eq_univ (n : ℕ) :
    Set.range (@DecisionTree.eval n) = Set.univ := by
  ext rule
  constructor
  · intro _
    trivial
  · intro _
    rcases evalDecisionTree_surjective n rule with ⟨tree, rfl⟩
    exact ⟨tree, rfl⟩

/-- The fixed-depth perfect-tree architecture viewed as one indexed predictor
family on `n` visible bits. -/
def decisionTreeIndexedFamily (n : ℕ) :
    IndexedPredictorFamily (DecisionTree n) (VisibleBits n) where
  predict := DecisionTree.eval

/-- This indexed family already realizes every Boolean rule on `n` visible bits. -/
theorem decisionTreeIndexedFamily_surjective (n : ℕ) :
    Function.Surjective (decisionTreeIndexedFamily n).predict := by
  simpa [decisionTreeIndexedFamily] using evalDecisionTree_surjective n

/-- Therefore the exact same-route notion also fails below the truth-table
threshold: depth-`n` decision-tree semantics have no exact bit budget below
`2^n`. -/
theorem not_decisionTreeIndexedFamily_hasBitBudget_of_lt {n s : ℕ}
    (hs : s < 2 ^ n) :
    ¬ (decisionTreeIndexedFamily n).HasBitBudget s := by
  exact
    IndexedPredictorFamily.not_hasBitBudget_of_surjective_predict
      (G := decisionTreeIndexedFamily n) hs (decisionTreeIndexedFamily_surjective n)

/-- The lower bound is sharp: truth-table coding yields an exact `2^n`-bit
budget for all depth-`n` decision-tree semantics. -/
theorem decisionTreeIndexedFamily_hasBitBudget_truthTable (n : ℕ) :
    (decisionTreeIndexedFamily n).HasBitBudget (2 ^ n) := by
  simpa [decisionTreeIndexedFamily, card_visibleBits] using
    IndexedPredictorFamily.hasBitBudget_card_of_fintype
      (H := decisionTreeIndexedFamily n)

/-- Quantitative form: any exact bit budget covering all depth-`n`
decision-tree semantics must use at least `2^n` bits. -/
theorem decisionTreeIndexedFamily_bitBudget_lowerBound {n s : ℕ}
    (hbudget : (decisionTreeIndexedFamily n).HasBitBudget s) :
    2 ^ n ≤ s := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict
      (G := decisionTreeIndexedFamily n) (decisionTreeIndexedFamily_surjective n) hbudget

/-- Therefore no `s`-bit exact code can cover the semantics of all depth-`n`
perfect decision trees once `s < 2^n`. -/
theorem no_surjective_bitCode_to_decisionTreeSemantics_of_lt {n s : ℕ}
    (decode : BitCode s → DecisionTree n) (hs : s < 2 ^ n) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (decode code)) := by
  exact not_surjective_decode_to_fullLocalRule_of_lt (decode := fun code => DecisionTree.eval (decode code)) hs

/-- Any finite message/state space whose interpreter covers all exact depth-`n`
tree semantics must contain at least one state for every local Boolean rule. -/
theorem localRule_card_le_of_surjective_treeMessageInterpreter
    {n : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree n)
    (hsurj : Function.Surjective (fun state => DecisionTree.eval (interpret state))) :
    2 ^ (2 ^ n) ≤ Fintype.card State := by
  have hcard : Fintype.card (LocalRule n) ≤ Fintype.card State :=
    Fintype.card_le_of_surjective (fun state => DecisionTree.eval (interpret state)) hsurj
  rw [card_localRule] at hcard
  exact hcard

/-- A finite message/state space below the local-rule cardinality cannot
interpret onto all exact tree semantics. -/
theorem not_surjective_treeMessageInterpreter_of_stateCard_lt
    {n : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree n)
    (hcard : Fintype.card State < 2 ^ (2 ^ n)) :
    ¬ Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
  intro hsurj
  exact Nat.not_lt_of_ge
    (localRule_card_le_of_surjective_treeMessageInterpreter interpret hsurj) hcard

/-- Factoring a code through a smaller finite tree-message state space cannot
cover all exact depth-`n` tree semantics. -/
theorem not_surjective_quotientCode_treeMessageInterpreter_of_stateCard_lt
    {n s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → DecisionTree n)
    (hcard : Fintype.card State < 2 ^ (2 ^ n)) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (interpret (decode code))) := by
  intro hsurj
  have hinterpret : Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
    intro rule
    rcases hsurj rule with ⟨code, hcode⟩
    exact ⟨decode code, hcode⟩
  exact not_surjective_treeMessageInterpreter_of_stateCard_lt interpret hcard hinterpret

/-- Binary-log specialization: even exact semantics of depth-`log₂ m + 1`
perfect trees cannot be coded below `m` bits. -/
theorem no_small_exact_treeQuotient_binaryLogWidth {m s : ℕ}
    (decode : BitCode s → DecisionTree (Nat.log 2 m + 1)) (hs : s < m) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (decode code)) := by
  apply no_surjective_bitCode_to_decisionTreeSemantics_of_lt decode
  exact Nat.lt_trans hs (Nat.lt_pow_succ_log_self Nat.one_lt_two m)

/-- At binary-log depth, exact tree-message coverage already forces at least
`2^m` finite message states. -/
theorem treeMessage_stateCard_lowerBound_binaryLogDepth {m : ℕ} {State : Type*}
    [Fintype State]
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hsurj : Function.Surjective (fun state => DecisionTree.eval (interpret state))) :
    2 ^ m ≤ Fintype.card State := by
  have hpow :
      2 ^ m ≤ 2 ^ (2 ^ (Nat.log 2 m + 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.lt_pow_succ_log_self Nat.one_lt_two m).le
  exact hpow.trans
    (localRule_card_le_of_surjective_treeMessageInterpreter interpret hsurj)

/-- Therefore, at binary-log tree depth, a finite message/state space with fewer
than `2^m` states cannot cover all exact tree semantics. -/
theorem not_surjective_treeMessageInterpreter_of_stateCard_lt_binaryLogDepth
    {m : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
  intro hsurj
  exact Nat.not_lt_of_ge
    (treeMessage_stateCard_lowerBound_binaryLogDepth interpret hsurj) hcard

/-- The same binary-log obstruction for a code that first chooses a finite
tree-message state and then interprets that state. -/
theorem not_surjective_quotientCode_treeMessageInterpreter_of_stateCard_lt_binaryLogDepth
    {m s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (interpret (decode code))) := by
  intro hsurj
  have hinterpret : Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
    intro rule
    rcases hsurj rule with ⟨code, hcode⟩
    exact ⟨decode code, hcode⟩
  exact
    not_surjective_treeMessageInterpreter_of_stateCard_lt_binaryLogDepth
      interpret hcard hinterpret

end Mettapedia.Computability.PNP
