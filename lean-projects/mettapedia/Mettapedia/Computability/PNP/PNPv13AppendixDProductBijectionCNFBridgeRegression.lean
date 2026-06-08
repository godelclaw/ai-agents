import Mettapedia.Computability.PNP.PNPv13AppendixDProductBijectionCNFBridge

/-!
# Regression checks for bijective CNF realization of Appendix D product witnesses
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

theorem bijective_product_cnf_readout_iff_valid_messages_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductBijectionCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (Y : Public) :
    SingleMessageReadout
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) ↔
      D.ValidProductWitnessSingleMessage Y :=
  D.singleMessageReadout_iff_validProductWitnessSingleMessage Y

theorem bijective_product_valid_messages_from_lock_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
    {Message : Type x} {Public : Type y} {RawGauge : Type z}
    {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}
    (D : AppendixDProductBijectionCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    D.ValidProductWitnessSingleMessage Y :=
  D.validProductWitnessSingleMessage_of_lockedMessageRigidity hrigid hY

theorem bijective_countermodel_extract_encode_regression
    {W : bijectiveAmbiguousAppendixDProductConstruction.Witness}
    (hW : bijectiveAmbiguousAppendixDProductConstruction.ValidWitness () W) :
    extractBijectiveAmbiguousProductWitness
        (encodeBijectiveAmbiguousProductWitness W) = W :=
  extract_encode_bijectiveAmbiguousProductWitness hW

theorem bijective_countermodel_encode_extract_regression
    {α : ConcreteCNF.Assignment (Fin 1)}
    (hα : ConcreteCNF.IsSatFormula oneVarTautologyCNF α) :
    encodeBijectiveAmbiguousProductWitness
        (extractBijectiveAmbiguousProductWitness α) = α :=
  encode_extract_bijectiveAmbiguousProductWitness hα

theorem bijective_countermodel_not_valid_message_single_regression :
    ¬ AppendixDProductBijectionCNFReadoutData.ValidProductWitnessSingleMessage
        bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData () :=
  bijectiveAmbiguousAppendixDProduct_not_validProductWitnessSingleMessage

theorem bijective_countermodel_not_single_readout_regression :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.formula ()))
      (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.projection ()) :=
  bijectiveAmbiguousAppendixDProduct_not_singleMessageReadout

theorem bijective_countermodel_not_correct_for_all_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.formula ()))
        (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.projection ())
        msg :=
  bijectiveAmbiguousAppendixDProduct_not_exists_correctForAll

theorem bijective_countermodel_not_lock_rigidity_regression :
    ¬ AppendixDLockedCore.LockedMessageRigidity
        bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.product.core :=
  bijectiveAmbiguousAppendixDProduct_not_lockedMessageRigidity

end Mettapedia.Computability.PNP
