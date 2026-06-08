import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadout

/-!
# Regression checks for manuscript-shaped v13 CNF readout constancy

These wrappers keep the exact Appendix I.23 dependency visible: CNF-level
readout constancy follows from the witness-level single-message promise, while
the compiler/extraction/projection interface alone admits a one-variable
countermodel.
-/

namespace Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutRegression

open Mettapedia.Computability.PNP

universe u v w x y z

theorem manuscript_single_message_promise_implies_cnf_constancy_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact D.singleMessageReadout_of_singleMessagePromise hpromise hY

theorem manuscript_single_message_promise_closes_arbitrary_sat_search_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    D.exists_correctForAllSatSearchOutputs_of_singleMessagePromise
      hpromise hY hα₀

theorem manuscript_supported_sat_search_equiv_single_message_under_complete_cnf_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  exact
    D.supportedArbitraryOutputSATSearchCorrect_iff_singleMessagePromise
      hsat hcomplete

theorem manuscript_complete_cnf_sat_search_forces_single_message_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    (hcorrect : D.SupportedArbitraryOutputSATSearchCorrect) :
    D.SingleMessagePromise := by
  exact
    D.singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
      hcomplete hcorrect

theorem distinct_valid_witness_messages_block_promise_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SingleMessagePromise := by
  exact
    D.not_singleMessagePromise_of_distinct_valid_witnessMessages
      hY hW hW' hdiff

theorem distinct_valid_witness_messages_block_supported_sat_search_when_complete_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    D.not_supportedArbitraryOutputSATSearchCorrect_of_complete_distinct_valid_witnessMessages
      hcomplete hY hW hW' hdiff

theorem locked_layer_rigidity_implies_witness_promise_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {Message : Type z}
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity) :
    D.toManuscriptCNFReadoutData.SingleMessagePromise := by
  exact D.singleMessagePromise_of_lockedLayerRigidity hrigid

theorem locked_layer_rigidity_implies_cnf_constancy_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {Message : Type z}
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact D.singleMessageReadout_of_lockedLayerRigidity hrigid hY

theorem locked_layer_rigidity_closes_arbitrary_sat_search_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {Message : Type z}
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact D.exists_correctForAllSatSearchOutputs_of_lockedLayerRigidity hrigid hY hα₀

theorem distinct_accepted_lock_messages_block_rigidity_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {Message : Type z}
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.lockMessage Y L ≠ D.lockMessage Y L') :
    ¬ D.LockedLayerRigidity := by
  exact
    D.not_lockedLayerRigidity_of_distinct_accepted_lockMessages
      hY hL hL' hdiff

theorem deterministic_readout_with_state_constancy_implies_rigidity_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {ReadState : Public → Type y} {Message : Type z}
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    (hstate : D.AcceptedReadStateConstancy) :
    D.toLockedLayerCNFReadoutData.LockedLayerRigidity := by
  exact D.lockedLayerRigidity_of_acceptedReadStateConstancy hstate

theorem deterministic_readout_with_state_constancy_closes_sat_search_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {ReadState : Public → Type y} {Message : Type z}
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    (hstate : D.AcceptedReadStateConstancy)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    D.exists_correctForAllSatSearchOutputs_of_acceptedReadStateConstancy
      hstate hY hα₀

theorem distinct_accepted_read_states_block_state_constancy_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {LockView : Public → Type x}
    {ReadState : Public → Type y} {Message : Type z}
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.readState Y L ≠ D.readState Y L') :
    ¬ D.AcceptedReadStateConstancy := by
  exact
    D.not_acceptedReadStateConstancy_of_distinct_accepted_readStates
      hY hL hL' hdiff

theorem ambiguous_countermodel_is_supported_regression :
    ambiguousOneVarManuscriptCNFReadoutData.support () := by
  exact ambiguousOneVarManuscriptCNFReadoutData_support

theorem ambiguous_countermodel_is_satisfiable_regression :
    ∃ α : ConcreteCNF.Assignment (oneVarReadoutPublicVar ()),
      ConcreteCNF.IsSatFormula
        (ambiguousOneVarManuscriptCNFReadoutData.formula ()) α := by
  exact ambiguousOneVarManuscriptCNFReadoutData_satisfiable

theorem ambiguous_countermodel_supported_satisfiable_regression :
    ambiguousOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  exact ambiguousOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable

theorem ambiguous_countermodel_complete_extraction_regression :
    ambiguousOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact ambiguousOneVarManuscriptCNFReadoutData_cnfExtractionComplete

theorem compiler_shape_without_promise_has_countermodel_regression :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact ambiguousOneVarManuscriptCNFReadoutData_not_singleMessagePromise

theorem complete_compiler_shape_without_promise_no_supported_sat_search_regression :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact ambiguousOneVarManuscriptCNFReadoutData_not_supportedArbitraryOutputSATSearchCorrect

theorem unrepresented_witness_countermodel_supported_satisfiable_regression :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  exact unrepresentedOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable

theorem unrepresented_witness_countermodel_cnf_readout_constant_regression :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (unrepresentedOneVarManuscriptCNFReadoutData.formula ()))
      (unrepresentedOneVarManuscriptCNFReadoutData.projection ()) := by
  exact unrepresentedOneVarManuscriptCNFReadoutData_singleMessageReadout

theorem unrepresented_witness_countermodel_supported_sat_search_correct_regression :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect

theorem unrepresented_witness_countermodel_not_single_message_regression :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise

theorem unrepresented_witness_countermodel_not_complete_regression :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact unrepresentedOneVarManuscriptCNFReadoutData_not_cnfExtractionComplete

theorem sat_search_without_complete_extraction_does_not_force_single_message_regression :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    unrepresentedOneVarManuscriptCNFReadoutData_satSearchCorrect_and_not_singleMessagePromise

theorem compiler_shape_without_promise_no_arbitrary_sat_search_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarManuscriptCNFReadoutData.formula ()))
        (ambiguousOneVarManuscriptCNFReadoutData.projection ()) msg := by
  exact ambiguousOneVarManuscriptCNFReadoutData_not_exists_correctForAll

theorem locked_layer_shape_without_rigidity_has_countermodel_regression :
    ¬ ambiguousOneVarLockedLayerCNFReadoutData.LockedLayerRigidity := by
  exact ambiguousOneVarLockedLayerCNFReadoutData_not_lockedLayerRigidity

theorem locked_layer_shape_without_rigidity_no_arbitrary_sat_search_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarLockedLayerCNFReadoutData.formula ()))
        (ambiguousOneVarLockedLayerCNFReadoutData.projection ()) msg := by
  exact ambiguousOneVarLockedLayerCNFReadoutData_not_exists_correctForAll

theorem deterministic_readout_without_state_constancy_has_countermodel_regression :
    ¬ ambiguousOneVarDeterministicReadoutLockedLayerData.AcceptedReadStateConstancy := by
  exact ambiguousOneVarDeterministicReadoutLockedLayerData_not_acceptedReadStateConstancy

theorem deterministic_readout_without_state_constancy_no_sat_search_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarDeterministicReadoutLockedLayerData.formula ()))
        (ambiguousOneVarDeterministicReadoutLockedLayerData.projection ()) msg := by
  exact ambiguousOneVarDeterministicReadoutLockedLayerData_not_exists_correctForAll

end Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadoutRegression
