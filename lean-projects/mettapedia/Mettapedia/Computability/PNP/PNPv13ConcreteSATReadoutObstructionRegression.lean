import Mettapedia.Computability.PNP.PNPv13ConcreteSATReadoutObstruction

/-!
# Regression checks for the concrete v13 CNF readout obstruction

These wrappers keep the one-variable CNF instantiation visible: a tautological
CNF can have multiple satisfying assignments with different message readouts,
so selected-witness correctness does not imply correctness for arbitrary
SAT-search output.
-/

namespace Mettapedia.Computability.PNP.PNPv13ConcreteSATReadoutObstructionRegression

open Mettapedia.Computability.PNP

universe u v

theorem one_var_tautology_false_assignment_satisfies_regression :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF oneVarFalseAssignment := by
  exact oneVarTautologyCNF_satisfied_false

theorem one_var_tautology_true_assignment_satisfies_regression :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF oneVarTrueAssignment := by
  exact oneVarTautologyCNF_satisfied_true

theorem one_var_tautology_has_distinct_readouts_regression :
    ∃ σ₁ σ₂ : ConcreteCNF.Assignment (Fin 1),
      ConcreteCNF.IsSatFormula oneVarTautologyCNF σ₁ ∧
      ConcreteCNF.IsSatFormula oneVarTautologyCNF σ₂ ∧
      oneVarReadout σ₁ ≠ oneVarReadout σ₂ := by
  exact oneVarTautologyCNF_has_distinct_satisfying_readouts

theorem cnf_arbitrary_output_message_forces_constancy_regression
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    (h :
      ∃ msg : Message,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula formula) readout msg) :
    SingleMessageReadout (ConcreteCNF.IsSatFormula formula) readout := by
  exact cnf_singleMessageReadout_of_exists_correctForAllSatSearchOutputs h

theorem cnf_readout_constancy_closes_arbitrary_output_sat_search_regression
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    {σ₀ : ConcreteCNF.Assignment Var}
    (hσ₀ : ConcreteCNF.IsSatFormula formula σ₀)
    (hconst : SingleMessageReadout
      (ConcreteCNF.IsSatFormula formula) readout) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula formula) readout msg := by
  exact
    cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
      hσ₀ hconst

theorem cnf_arbitrary_output_sat_search_iff_constancy_regression
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    {σ₀ : ConcreteCNF.Assignment Var}
    (hσ₀ : ConcreteCNF.IsSatFormula formula σ₀) :
    (∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula formula) readout msg) ↔
      SingleMessageReadout (ConcreteCNF.IsSatFormula formula) readout := by
  exact
    cnf_exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_satisfying_assignment
      hσ₀

theorem one_var_tautology_not_single_message_regression :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout := by
  exact oneVarTautologyCNF_not_singleMessageReadout

theorem one_var_tautology_no_fixed_message_regression :
    ¬ ∃ msg : Bool,
      FixedMessageReadout
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact oneVarTautologyCNF_not_exists_fixedMessageReadout

theorem one_var_tautology_no_arbitrary_sat_search_output_message_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs

theorem one_var_tautology_selected_output_correct_for_both_messages_regression :
    CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout false ∧
      CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout true := by
  exact oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true

theorem one_var_tautology_selected_output_correct_not_arbitrary_output_correct_regression :
    (∃ msg : Bool,
      CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg) ∧
      ¬ ∃ msg : Bool,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact oneVarTautologyCNF_correctForSomeSatSearchOutput_not_correctForAll

end Mettapedia.Computability.PNP.PNPv13ConcreteSATReadoutObstructionRegression
