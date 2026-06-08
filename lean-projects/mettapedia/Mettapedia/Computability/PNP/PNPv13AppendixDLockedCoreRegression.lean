import Mettapedia.Computability.PNP.PNPv13AppendixDLockedCore

/-!
# Regression checks for Appendix D locked-core readout

These wrappers keep the manuscript dependency precise: Appendix D.8
locked-message rigidity closes the witness and CNF readout route, while
Appendix D.5--D.7 plus deterministic readout do not imply D.8.
-/

namespace Mettapedia.Computability.PNP.PNPv13AppendixDLockedCoreRegression

open Mettapedia.Computability.PNP

universe u v w x y z

theorem appendixD_lock_satisfiable_and_rigid_gives_locked_message_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (hsat : C.LockSatisfiable)
    (hrigid : C.LockedMessageRigidity)
    {Y : PublicLock} (hY : C.support Y) :
    ∃ msg : Message, C.LockedMessageSpec Y msg := by
  exact C.exists_lockedMessageSpec_of_lockSatisfiable_of_lockedMessageRigidity
    hsat hrigid hY

theorem appendixD_rigidity_implies_witness_promise_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Witness : Public → Type y}
    (D : AppendixDWitnessData
      PublicLock Quotient LockAux Message Public Witness)
    (hrigid : D.core.LockedMessageRigidity) :
    D.SingleMessagePromise := by
  exact D.singleMessagePromise_of_lockedMessageRigidity hrigid

theorem appendixD_rigidity_gives_public_message_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Witness : Public → Type y}
    (D : AppendixDWitnessData
      PublicLock Quotient LockAux Message Public Witness)
    (hwit : D.WitnessExistsOnSupport)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message, D.PublicMessageSpec Y msg := by
  exact D.exists_publicMessageSpec_of_lockedMessageRigidity hwit hrigid hY

theorem appendixI_rigidity_implies_cnf_readout_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public → Type y} {Witness : Public → Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact D.singleMessageReadout_of_lockedMessageRigidity hrigid hY

theorem appendixI_rigidity_gives_projected_message_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public → Type y} {Witness : Public → Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message, D.ProjectedMessageSpec Y msg := by
  exact D.exists_projectedMessageSpec_of_lockedMessageRigidity hrigid hY

theorem appendixI_rigidity_gives_i26_semantic_items_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public → Type y} {Witness : Public → Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    (∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α) ∧
    (∀ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α →
        D.validWitness Y (D.extract Y α)) ∧
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact D.semantic_i26_items_of_lockedMessageRigidity hrigid hY

theorem appendixI_rigidity_closes_arbitrary_sat_search_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public → Type y} {Witness : Public → Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact D.exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity
    hrigid hY

theorem appendixD_distinct_completions_block_rigidity_regression
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    {Y : PublicLock} (hY : C.support Y)
    (L L' : C.LockedCompletion Y)
    (hdiff : L.message ≠ L'.message) :
    ¬ C.LockedMessageRigidity := by
  exact C.not_lockedMessageRigidity_of_distinct_completions hY L L' hdiff

theorem appendixD_countermodel_satisfies_D7_regression :
    ambiguousAppendixDLockedCore.LockSatisfiable := by
  exact ambiguousAppendixDLockedCore_lockSatisfiable

theorem appendixD_countermodel_has_deterministic_readout_regression :
    ambiguousAppendixDLockedCore.ReadDeterministic := by
  exact ambiguousAppendixDLockedCore_readDeterministic

theorem appendixD_countermodel_not_D8_regression :
    ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact ambiguousAppendixDLockedCore_not_lockedMessageRigidity

theorem appendixD_witness_countermodel_not_promise_regression :
    ¬ ambiguousAppendixDWitnessData.SingleMessagePromise := by
  exact ambiguousAppendixDWitnessData_not_singleMessagePromise

theorem appendixI_countermodel_no_arbitrary_sat_search_regression :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixICNFReadoutData.formula ()))
        (ambiguousAppendixICNFReadoutData.projection ()) msg := by
  exact ambiguousAppendixICNFReadoutData_not_exists_correctForAll

end Mettapedia.Computability.PNP.PNPv13AppendixDLockedCoreRegression
