import Mettapedia.Computability.PNP.PNPv13AppendixDProductExactCNFBridge

/-!
# Regression checks for exact CNF realization of Appendix D product witnesses
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

theorem exact_product_cnf_distinct_valid_witnesses_block_readout_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.not_singleMessageReadout_of_distinct_valid_witnessMessages hW hW' hdiff

theorem exact_product_cnf_distinct_valid_witnesses_block_correct_for_all_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg :=
  D.not_exists_correctForAllSatSearchOutputs_of_distinct_valid_witnessMessages
    hW hW' hdiff

theorem exact_product_cnf_distinct_valid_witnesses_block_lock_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hY : D.product.support Y)
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ D.product.core.LockedMessageRigidity :=
  D.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
    hY hW hW' hdiff

theorem one_var_tautology_any_assignment_regression
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF σ :=
  oneVarTautologyCNF_satisfied_any σ

theorem exact_product_cnf_countermodel_messages_differ_regression :
    ambiguousAppendixDProductWitnessFalse.message ≠
      ambiguousAppendixDProductWitnessTrue.message :=
  ambiguousAppendixDProductWitnessFalse_message_ne_true

theorem exact_product_cnf_countermodel_not_single_readout_regression :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (ambiguousAppendixDProductExactCNFReadoutData.formula ()))
      (ambiguousAppendixDProductExactCNFReadoutData.projection ()) :=
  ambiguousAppendixDProductExactCNFReadoutData_not_singleMessageReadout

theorem exact_product_cnf_countermodel_not_correct_for_all_regression :
    ¬ ∃ msg : Unit → Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixDProductExactCNFReadoutData.formula ()))
        (ambiguousAppendixDProductExactCNFReadoutData.projection ()) msg :=
  ambiguousAppendixDProductExactCNFReadoutData_not_exists_correctForAll

theorem exact_product_cnf_countermodel_not_lock_rigidity_regression :
    ¬ ambiguousAppendixDProductExactCNFReadoutData.product.core.LockedMessageRigidity :=
  ambiguousAppendixDProductExactCNFReadoutData_not_lockedMessageRigidity

end Mettapedia.Computability.PNP
