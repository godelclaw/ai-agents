import Mettapedia.Computability.PNP.PNPv13AppendixDProductConstruction

/-!
# Regression tests for the Appendix D product construction

These checks keep the D.36--D.41 product layer honest: product single-message
readout is inherited from locked-core rigidity, and the neutral-public one-bit
locked-core countermodel lifts through trivial gauge, buffer, and auxiliary
clauses.
-/

namespace Mettapedia.Computability.PNP

theorem product_single_message_from_lock_rigidity_regression
    {PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux : Type}
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    (hrigid : D.core.LockedMessageRigidity) :
    ∀ {Y : Public} {W W' : D.Witness},
      D.support Y →
        D.ValidWitness Y W →
          D.ValidWitness Y W' →
            W.message = W'.message :=
  D.singleMessagePromise_of_lockedMessageRigidity hrigid

theorem product_distinct_messages_block_lock_rigidity_regression
    {PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux : Type}
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    {Y : Public} {W W' : D.Witness}
    (hY : D.support Y)
    (hW : D.ValidWitness Y W) (hW' : D.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ D.core.LockedMessageRigidity :=
  D.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
    hY hW hW' hdiff

theorem product_countermodel_false_valid_regression :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      ambiguousAppendixDProductWitnessFalse :=
  ambiguousAppendixDProductWitnessFalse_valid

theorem product_countermodel_true_valid_regression :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      ambiguousAppendixDProductWitnessTrue :=
  ambiguousAppendixDProductWitnessTrue_valid

theorem product_countermodel_not_lock_rigidity_regression :
    ¬ ambiguousAppendixDProductConstruction.core.LockedMessageRigidity :=
  ambiguousAppendixDProductConstruction_not_lockedMessageRigidity

end Mettapedia.Computability.PNP
