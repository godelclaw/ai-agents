import Mettapedia.Computability.PNP.MetagraphObstruction

/-!
# Regression checks for exact metagraph/interface quotient obstructions

These checks pin the two-stage quotient repair: a large code space may choose a
finite quotient state, and an interpreter may map that state to exact boundary
behavior.  Exact coverage still forces the quotient state space itself to be as
large as the full boundary-map class.
-/

namespace Mettapedia.Computability.PNP.MetagraphObstructionRegression

open Mettapedia.Computability.PNP

theorem boundary_map_card_le_of_surjective_interpret_regression
    {k : ℕ} {State : Type*} [Fintype State]
    (interpret : State → BoundaryMap k)
    (hsurj : Function.Surjective interpret) :
    2 ^ (k * 2 ^ k) ≤ Fintype.card State := by
  exact boundaryMap_card_le_of_surjective_interpret interpret hsurj

theorem not_surjective_interpret_boundary_map_of_state_card_lt_regression
    {k : ℕ} {State : Type*} [Fintype State]
    (interpret : State → BoundaryMap k)
    (hcard : Fintype.card State < 2 ^ (k * 2 ^ k)) :
    ¬ Function.Surjective interpret := by
  exact not_surjective_interpret_boundaryMap_of_stateCard_lt interpret hcard

theorem not_surjective_quotient_code_boundary_map_of_state_card_lt_regression
    {k s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → BoundaryMap k)
    (hcard : Fintype.card State < 2 ^ (k * 2 ^ k)) :
    ¬ Function.Surjective (fun code => interpret (decode code)) := by
  exact not_surjective_quotientCode_boundaryMap_of_stateCard_lt
    decode interpret hcard

theorem boundary_map_state_card_lower_bound_binary_log_width_regression
    {m : ℕ} {State : Type*} [Fintype State]
    (interpret : State → BoundaryMap (Nat.log 2 m + 1))
    (hsurj : Function.Surjective interpret) :
    2 ^ m ≤ Fintype.card State := by
  exact boundaryMap_stateCard_lowerBound_binaryLogWidth interpret hsurj

theorem not_surjective_interpret_boundary_map_of_state_card_lt_input_size_regression
    {m : ℕ} {State : Type*} [Fintype State]
    (interpret : State → BoundaryMap (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective interpret := by
  exact
    not_surjective_interpret_boundaryMap_of_stateCard_lt_inputSize_binaryLogWidth
      interpret hcard

theorem not_surjective_quotient_code_boundary_map_of_state_card_lt_input_size_regression
    {m s : ℕ} {State : Type*} [Fintype State]
    (decode : BitCode s → State)
    (interpret : State → BoundaryMap (Nat.log 2 m + 1))
    (hcard : Fintype.card State < 2 ^ m) :
    ¬ Function.Surjective (fun code => interpret (decode code)) := by
  exact
    not_surjective_quotientCode_boundaryMap_of_stateCard_lt_inputSize_binaryLogWidth
      decode interpret hcard

end Mettapedia.Computability.PNP.MetagraphObstructionRegression
