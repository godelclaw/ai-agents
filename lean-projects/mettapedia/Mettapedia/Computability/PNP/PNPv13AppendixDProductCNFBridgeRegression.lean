import Mettapedia.Computability.PNP.PNPv13AppendixDProductCNFBridge

/-!
# Regression checks for the Appendix D product / Appendix I CNF bridge
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

theorem product_cnf_readout_constancy_from_lock_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.singleMessageReadout_of_lockedMessageRigidity hrigid hY

theorem product_cnf_correct_for_all_from_lock_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg :=
  D.exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity hrigid hY

theorem product_cnf_distinct_satisfying_projections_block_lock_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {α β : ConcreteCNF.Assignment (Var Y)}
    (hY : D.product.support Y)
    (hα : ConcreteCNF.IsSatFormula (D.formula Y) α)
    (hβ : ConcreteCNF.IsSatFormula (D.formula Y) β)
    (hdiff : D.projection Y α ≠ D.projection Y β) :
    ¬ D.product.core.LockedMessageRigidity :=
  D.not_lockedMessageRigidity_of_distinct_satisfying_projections
    hY hα hβ hdiff

theorem product_cnf_countermodel_false_projection_ne_true_regression :
    oneVarSingletonBlockReadout oneVarFalseAssignment ≠
      oneVarSingletonBlockReadout oneVarTrueAssignment :=
  oneVarSingletonBlockReadout_false_ne_true

theorem product_cnf_countermodel_assignment_extract_valid_regression
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      (ambiguousAppendixDProductWitnessOfAssignment σ) :=
  ambiguousAppendixDProductWitnessOfAssignment_valid σ

theorem product_cnf_countermodel_not_lock_rigidity_regression :
    ¬ ambiguousAppendixDProductCNFReadoutData.product.core.LockedMessageRigidity :=
  ambiguousAppendixDProductCNFReadoutData_not_lockedMessageRigidity

theorem product_cnf_countermodel_not_correct_for_all_regression :
    ¬ ∃ msg : Unit → Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixDProductCNFReadoutData.formula ()))
        (ambiguousAppendixDProductCNFReadoutData.projection ()) msg :=
  ambiguousAppendixDProductCNFReadoutData_not_exists_correctForAll

end Mettapedia.Computability.PNP
