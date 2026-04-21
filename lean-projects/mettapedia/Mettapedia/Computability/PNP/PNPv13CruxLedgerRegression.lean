import Mettapedia.Computability.PNP.PNPv13CruxLedger

/-!
# Regression checks for the PNP v13 crux ledger

These checks pin two v13 crux attacks: the `P=NP` upper-bound decoder requires a
single-message/readout-constancy theorem for arbitrary satisfying SAT-search
outputs, and unconditional half-success marginals do not imply product decay
without a sequential conditional hypothesis.
-/

namespace Mettapedia.Computability.PNP.PNPv13CruxLedgerRegression

open Mettapedia.Computability.PNP

universe u v

theorem fixed_message_implies_single_message_regression
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : FixedMessageReadout sat readout msg) :
    SingleMessageReadout sat readout := by
  exact singleMessageReadout_of_fixedMessageReadout h

theorem single_message_with_witness_implies_fixed_message_regression
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness}
    (hw₀ : sat w₀)
    (h : SingleMessageReadout sat readout) :
    FixedMessageReadout sat readout (readout w₀) := by
  exact fixedMessageReadout_of_singleMessageReadout hw₀ h

theorem search_outputs_correct_iff_fixed_message_regression
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message} :
    CorrectForAllSatSearchOutputs sat readout msg ↔
      FixedMessageReadout sat readout msg := by
  exact correctForAllSatSearchOutputs_iff_fixedMessageReadout

theorem search_outputs_correct_implies_single_message_regression
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : CorrectForAllSatSearchOutputs sat readout msg) :
    SingleMessageReadout sat readout := by
  exact singleMessageReadout_of_correctForAllSatSearchOutputs h

theorem search_outputs_correct_iff_single_message_with_witness_regression
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness}
    (hw₀ : sat w₀) :
    CorrectForAllSatSearchOutputs sat readout (readout w₀) ↔
      SingleMessageReadout sat readout := by
  exact correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness hw₀

theorem bool_true_id_not_single_message_regression :
    ¬ SingleMessageReadout (fun _ : Bool => True) (fun w : Bool => w) := by
  exact not_singleMessageReadout_bool_true_id

theorem bool_true_id_has_distinct_satisfying_readouts_regression :
    ∃ w₁ w₂ : Bool,
      (fun _ : Bool => True) w₁ ∧
      (fun _ : Bool => True) w₂ ∧
      (fun w : Bool => w) w₁ ≠ (fun w : Bool => w) w₂ := by
  exact exists_two_satisfying_outputs_with_distinct_readouts_bool_true_id

theorem bool_true_id_has_distinct_sat_search_outputs_regression :
    ∃ out₁ out₂ : SatSearchOutput (fun _ : Bool => True),
      (fun w : Bool => w) out₁.witness ≠ (fun w : Bool => w) out₂.witness := by
  exact exists_two_satSearchOutputs_with_distinct_readouts_bool_true_id

theorem bool_true_id_no_fixed_message_regression :
    ¬ ∃ msg : Bool,
      FixedMessageReadout (fun _ : Bool => True) (fun w : Bool => w) msg := by
  exact not_exists_fixedMessageReadout_bool_true_id

theorem bool_true_id_no_search_output_message_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (fun _ : Bool => True) (fun w : Bool => w) msg := by
  exact not_exists_correctForAllSatSearchOutputs_bool_true_id

theorem bool_success_event_count_regression :
    boolEventCount boolSuccessEvent = 1 := by
  exact boolSuccessEvent_count

theorem bool_success_event_joint_count_regression :
    boolJointEventCount boolSuccessEvent boolSuccessEvent = 1 := by
  exact boolSuccessEvent_joint_count

theorem correlated_half_marginals_violate_quarter_product_bound_regression :
    boolEventCount boolSuccessEvent = 1 ∧
      boolEventCount boolSuccessEvent = 1 ∧
      ¬ 4 * boolJointEventCount boolSuccessEvent boolSuccessEvent ≤ 2 := by
  exact correlated_half_marginals_violate_quarter_product_bound

theorem bool_pair_product_bound_of_sequential_half_regression
    (E F : Bool × Bool → Prop) [DecidablePred E] [DecidablePred F]
    (h : SequentialHalfOnBoolPair E F) :
    4 * boolPairJointEventCount E F ≤ 4 := by
  exact boolPair_product_bound_of_sequentialHalf E F h

theorem bool_pair_first_success_count_regression :
    boolPairEventCount boolPairFirstSuccess = 2 := by
  exact boolPairFirstSuccess_count

theorem bool_pair_second_success_count_regression :
    boolPairEventCount boolPairSecondSuccess = 2 := by
  exact boolPairSecondSuccess_count

theorem bool_pair_first_second_joint_count_regression :
    boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess = 1 := by
  exact boolPairFirstSecondSuccess_joint_count

theorem bool_pair_first_second_sequential_half_regression :
    SequentialHalfOnBoolPair boolPairFirstSuccess boolPairSecondSuccess := by
  exact boolPairFirstSecondSuccess_sequentialHalf

theorem bool_pair_first_second_product_bound_regression :
    4 * boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess ≤ 4 := by
  exact boolPairFirstSecondSuccess_product_bound

theorem bool_pair_correlated_marginals_violate_product_bound_regression :
    boolPairEventCount boolPairFirstSuccess = 2 ∧
      boolPairEventCount boolPairFirstSuccess = 2 ∧
      ¬ 4 * boolPairJointEventCount boolPairFirstSuccess boolPairFirstSuccess ≤ 4 := by
  exact boolPair_correlated_half_marginals_violate_product_bound

theorem bool_pair_correlated_marginals_fail_sequential_half_regression :
    ¬ SequentialHalfOnBoolPair boolPairFirstSuccess boolPairFirstSuccess := by
  exact boolPair_correlated_marginals_fail_sequentialHalf

end Mettapedia.Computability.PNP.PNPv13CruxLedgerRegression
