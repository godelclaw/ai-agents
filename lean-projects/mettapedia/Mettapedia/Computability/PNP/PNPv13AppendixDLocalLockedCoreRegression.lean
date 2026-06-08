import Mettapedia.Computability.PNP.PNPv13AppendixDLocalLockedCore

/-!
# Regression tests for the local Appendix D locked-core countermodel

These checks keep the Appendix D.5 bounded-local presentation tied to the
semantic obstruction: the one-bit local countermodel satisfies D.7 and
deterministic readout, yet it refutes D.8.
-/

namespace Mettapedia.Computability.PNP

theorem local_countermodel_satisfies_D7_regression :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore.LockSatisfiable :=
  ambiguousAppendixDLocalBoolLockedCore_lockSatisfiable

theorem local_countermodel_read_deterministic_regression :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore.ReadDeterministic :=
  ambiguousAppendixDLocalBoolLockedCore_readDeterministic

theorem local_countermodel_not_D8_regression :
    ¬ AppendixDLockedCore.LockedMessageRigidity
        ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore :=
  ambiguousAppendixDLocalBoolLockedCore_not_lockedMessageRigidity

theorem one_bit_read_predicate_is_arity_two_regression :
    ∀ C ∈ oneBitReadEqualsQuotientPredicate.constraints,
      C.scope.length ≤ oneBitReadEqualsQuotientPredicate.arityBound :=
  oneBitReadEqualsQuotientPredicate.bounded

end Mettapedia.Computability.PNP
