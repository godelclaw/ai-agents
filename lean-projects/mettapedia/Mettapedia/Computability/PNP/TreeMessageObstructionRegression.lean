import Mettapedia.Computability.PNP.TreeMessageObstruction

/-!
# Regression checks for tree-message interpreter obstructions

These wrappers pin the two-stage tree-message repair surface: a finite
message/state space may be decoded from a code and then interpreted as a depth
tree, but exact coverage of all tree semantics still forces the state space to
be as large as the full local-rule class.
-/

namespace Mettapedia.Computability.PNP.TreeMessageObstructionRegression

open Mettapedia.Computability.PNP

theorem eval_decision_tree_injective_regression (n : ℕ) :
    Function.Injective (@DecisionTree.eval n) := by
  exact evalDecisionTree_injective n

theorem eval_decision_tree_bijective_regression (n : ℕ) :
    Function.Bijective (@DecisionTree.eval n) := by
  exact evalDecisionTree_bijective n

theorem local_rule_card_le_of_surjective_tree_message_interpreter_regression
    {n : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree n)
    (hsurj : Function.Surjective (fun state => DecisionTree.eval (interpret state))) :
    2 ^ (2 ^ n) ≤ Fintype.card State := by
  exact localRule_card_le_of_surjective_treeMessageInterpreter interpret hsurj

theorem not_surjective_tree_message_interpreter_of_state_card_lt_regression
    {n : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree n)
    (hcard : Fintype.card State < 2 ^ (2 ^ n)) :
    ¬ Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
  exact not_surjective_treeMessageInterpreter_of_stateCard_lt interpret hcard

theorem not_surjective_quotient_code_tree_message_interpreter_of_state_card_lt_regression
    {n s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → DecisionTree n)
    (hcard : Fintype.card State < 2 ^ (2 ^ n)) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (interpret (decode code))) := by
  exact
    not_surjective_quotientCode_treeMessageInterpreter_of_stateCard_lt
      decode interpret hcard

theorem tree_message_state_card_lower_bound_binary_log_depth_regression
    {m : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hsurj : Function.Surjective (fun state => DecisionTree.eval (interpret state))) :
    2 ^ m ≤ Fintype.card State := by
  exact treeMessage_stateCard_lowerBound_binaryLogDepth interpret hsurj

theorem not_surjective_tree_message_interpreter_of_state_card_lt_binary_log_depth_regression
    {m : ℕ} {State : Type*} [Fintype State]
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective (fun state => DecisionTree.eval (interpret state)) := by
  exact
    not_surjective_treeMessageInterpreter_of_stateCard_lt_binaryLogDepth
      interpret hcard

theorem not_surjective_quotient_code_tree_message_interpreter_of_state_card_lt_binary_log_depth_regression
    {m s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → DecisionTree (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective (fun code => DecisionTree.eval (interpret (decode code))) := by
  exact
    not_surjective_quotientCode_treeMessageInterpreter_of_stateCard_lt_binaryLogDepth
      decode interpret hcard

end Mettapedia.Computability.PNP.TreeMessageObstructionRegression
