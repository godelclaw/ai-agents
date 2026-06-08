import Mathlib.Data.Fintype.Basic
import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadout

/-!
# PNP v13: Appendix D locked cores and Appendix I readout

This file formalizes the manuscript's Appendix D.5--D.8 locked-completion
surface and composes it with Appendix D.41--D.42 and Appendix I.23--I.26.

The important point is deliberately sharp: a locked completion is accepted only
when both the locked predicate and the readout predicate accept.  Appendix D.8
is then exactly the global theorem that all such completions over one supported
public lock syntax carry the same message.  The semantic Appendix I readout
bridge follows from D.8, while D.5--D.7 plus deterministic readout alone do not
imply D.8.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- Appendix D.5 locked quotient core data.  The finiteness fields record the
finite public syntax set, quotient index domain, auxiliary domain, and message
domain at one size parameter.  Bounded arity and polynomial-time decidability
are construction-level obligations outside the readout-constancy proof. -/
structure AppendixDLockedCore (PublicLock : Type u) (Quotient : Type v)
    (LockAux : Type w) (Message : Type z) where
  publicLockFinite : Fintype PublicLock
  quotientFinite : Fintype Quotient
  lockAuxFinite : Fintype LockAux
  messageFinite : Fintype Message
  /-- Public lock syntaxes in the sampler support. -/
  support : PublicLock → Prop
  /-- The Appendix D locked predicate `Lock_Y(z, ξ_lock, M)`. -/
  lockPredicate : PublicLock → Quotient → LockAux → Message → Prop
  /-- The Appendix D readout predicate `Read_Y(z, ξ_lock, M)`. -/
  readPredicate : PublicLock → Quotient → LockAux → Message → Prop

namespace AppendixDLockedCore

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}

/-- Appendix D.6: a locked completion is a triple satisfying both `Lock` and
`Read`. -/
structure LockedCompletion
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (Y : PublicLock) where
  quotient : Quotient
  lockAux : LockAux
  message : Message
  lock_ok : C.lockPredicate Y quotient lockAux message
  read_ok : C.readPredicate Y quotient lockAux message

/-- Appendix D.7: every supported public lock syntax has at least one locked
completion. -/
def LockSatisfiable
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) : Prop :=
  ∀ {Y : PublicLock}, C.support Y → Nonempty (C.LockedCompletion Y)

/-- Appendix D.8: any two locked completions over one supported public lock
syntax carry the same message. -/
def LockedMessageRigidity
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) : Prop :=
  ∀ {Y : PublicLock},
    C.support Y →
      (L L' : C.LockedCompletion Y) →
        L.message = L'.message

/-- Determinism of the readout predicate for a fixed `(Y,z,ξ_lock)` state.
This is weaker than Appendix D.8 because D.8 compares different completions. -/
def ReadDeterministic
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) : Prop :=
  ∀ {Y : PublicLock} {z : Quotient} {ξ : LockAux} {M M' : Message},
    C.readPredicate Y z ξ M →
      C.readPredicate Y z ξ M' →
        M = M'

/-- The proposition-level content of Appendix D.9: `msg` is the common message
of all locked completions of `Y`.  This avoids choosing a representative by
classical choice. -/
def LockedMessageSpec
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (Y : PublicLock) (msg : Message) : Prop :=
  ∀ L : C.LockedCompletion Y, L.message = msg

/-- Appendix D.10, existence form: D.7 and D.8 give a well-defined locked
message for every supported public lock syntax. -/
theorem exists_lockedMessageSpec_of_lockSatisfiable_of_lockedMessageRigidity
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (hsat : C.LockSatisfiable)
    (hrigid : C.LockedMessageRigidity)
    {Y : PublicLock} (hY : C.support Y) :
    ∃ msg : Message, C.LockedMessageSpec Y msg := by
  rcases hsat hY with ⟨L₀⟩
  exact ⟨L₀.message, fun L => hrigid hY L L₀⟩

/-- The common locked message is unique whenever a supported public lock syntax
has a locked completion. -/
theorem lockedMessageSpec_unique_of_lockSatisfiable
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (hsat : C.LockSatisfiable)
    {Y : PublicLock} (hY : C.support Y)
    {msg msg' : Message}
    (hmsg : C.LockedMessageSpec Y msg)
    (hmsg' : C.LockedMessageSpec Y msg') :
    msg = msg' := by
  rcases hsat hY with ⟨L⟩
  exact (hmsg L).symm.trans (hmsg' L)

/-- Exact D.8 obstruction: two locked completions with different messages refute
locked-message rigidity. -/
theorem not_lockedMessageRigidity_of_distinct_completions
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    {Y : PublicLock} (hY : C.support Y)
    (L L' : C.LockedCompletion Y)
    (hdiff : L.message ≠ L'.message) :
    ¬ C.LockedMessageRigidity := by
  intro hrigid
  exact hdiff (hrigid hY L L')

end AppendixDLockedCore

/-- Appendix D.41 witness layer: a valid witness determines a locked
completion for the public lock syntax carried by its public instance, and its
semantic witness message is the completion's message coordinate. -/
structure AppendixDWitnessData (PublicLock : Type u) (Quotient : Type v)
    (LockAux : Type w) (Message : Type z)
    (Public : Type x) (Witness : Public → Type y) where
  core : AppendixDLockedCore PublicLock Quotient LockAux Message
  support : Public → Prop
  publicLock : Public → PublicLock
  validWitness : (Y : Public) → Witness Y → Prop
  witnessMessage : (Y : Public) → Witness Y → Message
  /-- The locked/readout clauses extracted from a valid witness. -/
  witnessCompletion :
    ∀ {Y : Public}, (W : Witness Y) →
      validWitness Y W →
        core.LockedCompletion (publicLock Y)
  support_publicLock :
    ∀ {Y : Public}, support Y → core.support (publicLock Y)
  witnessMessage_eq_completionMessage :
    ∀ {Y : Public} {W : Witness Y} (hW : validWitness Y W),
      witnessMessage Y W = (witnessCompletion W hW).message

namespace AppendixDWitnessData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Witness : Public → Type y}

/-- The Appendix D.41 single-message promise at the witness relation. -/
def SingleMessagePromise
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness) :
    Prop :=
  ∀ {Y : Public} {W W' : Witness Y},
    D.support Y →
      D.validWitness Y W →
        D.validWitness Y W' →
          D.witnessMessage Y W = D.witnessMessage Y W'

/-- Appendix D.41: locked-message rigidity of the Appendix D core implies the
witness-level single-message promise. -/
theorem singleMessagePromise_of_lockedMessageRigidity
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness)
    (hrigid : D.core.LockedMessageRigidity) :
    D.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  calc
    D.witnessMessage Y W = (D.witnessCompletion W hW).message :=
      D.witnessMessage_eq_completionMessage hW
    _ = (D.witnessCompletion W' hW').message :=
      hrigid (D.support_publicLock hY) (D.witnessCompletion W hW)
        (D.witnessCompletion W' hW')
    _ = D.witnessMessage Y W' :=
      (D.witnessMessage_eq_completionMessage hW').symm

/-- Exact obstruction to Appendix D.41 at the witness layer. -/
theorem not_singleMessagePromise_of_distinct_valid_witnessMessages
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SingleMessagePromise := by
  intro hpromise
  exact hdiff (hpromise hY hW hW')

/-- Witness existence on supported public instances, the semantic part used in
Appendix D.42 to define the public-instance message. -/
def WitnessExistsOnSupport
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness) :
    Prop :=
  ∀ {Y : Public}, D.support Y → ∃ W : Witness Y, D.validWitness Y W

/-- Appendix D.42 proposition-level public message specification. -/
def PublicMessageSpec
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness)
    (Y : Public) (msg : Message) : Prop :=
  ∀ {W : Witness Y}, D.validWitness Y W → D.witnessMessage Y W = msg

/-- Appendix D.42, existence form: witness existence and D.8 define a unique
public-instance message. -/
theorem exists_publicMessageSpec_of_lockedMessageRigidity
    (D : AppendixDWitnessData PublicLock Quotient LockAux Message Public Witness)
    (hwit : D.WitnessExistsOnSupport)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message, D.PublicMessageSpec Y msg := by
  rcases hwit hY with ⟨W₀, hW₀⟩
  refine ⟨D.witnessMessage Y W₀, ?_⟩
  intro W hW
  exact D.singleMessagePromise_of_lockedMessageRigidity hrigid hY hW hW₀

end AppendixDWitnessData

/-- Appendix I semantic CNF realization data for the Appendix D locked-core
witness relation.  The uniform polynomial-time and size clauses of I.26(iv)
are not used by the message-constancy bridge; the fields here formalize the
semantic readout obligations I.23--I.26(i)--(iii). -/
structure AppendixICNFReadoutData (PublicLock : Type u) (Quotient : Type v)
    (LockAux : Type w) (Message : Type z)
    (Public : Type x) (Var : Public → Type y) (Witness : Public → Type y)
    extends AppendixDWitnessData
      PublicLock Quotient LockAux Message Public Witness where
  formula : (Y : Public) → ConcreteCNF.Formula (Var Y)
  extract : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Witness Y
  projection : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Message
  cnfSound :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        validWitness Y (extract Y α)
  projection_eq_witnessMessage :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        projection Y α = witnessMessage Y (extract Y α)
  satOnSupport :
    ∀ {Y : Public}, support Y → ∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (formula Y) α

namespace AppendixICNFReadoutData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public → Type y}
variable {Witness : Public → Type y}

/-- Forget the Appendix D locked-core fields to the Appendix I.23 CNF readout
interface. -/
def toManuscriptCNFReadoutData
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) :
    ManuscriptCNFReadoutData Public Var Witness Message where
  support := D.support
  formula := D.formula
  validWitness := D.validWitness
  extract := D.extract
  witnessMessage := D.witnessMessage
  projection := D.projection
  cnfSound := D.cnfSound
  projection_eq_witnessMessage := D.projection_eq_witnessMessage

/-- Appendix I.23/I.25: D.8 locked-message rigidity gives CNF-level
single-message readout for the fixed projection. -/
theorem singleMessageReadout_of_lockedMessageRigidity
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact
    D.toManuscriptCNFReadoutData.singleMessageReadout_of_singleMessagePromise
      (D.toAppendixDWitnessData.singleMessagePromise_of_lockedMessageRigidity
        hrigid) hY

/-- Appendix I.24/I.25, proposition-level form: under D.8 there is a projected
message for the public instance and every satisfying CNF assignment projects to
it. -/
def ProjectedMessageSpec
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (Y : Public) (msg : Message) : Prop :=
  ∀ {α : ConcreteCNF.Assignment (Var Y)},
    ConcreteCNF.IsSatFormula (D.formula Y) α →
      D.projection Y α = msg

/-- Appendix I.24/I.25, existence form. -/
theorem exists_projectedMessageSpec_of_lockedMessageRigidity
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message, D.ProjectedMessageSpec Y msg := by
  rcases D.satOnSupport hY with ⟨α₀, hα₀⟩
  refine ⟨D.projection Y α₀, ?_⟩
  intro α hα
  exact D.singleMessageReadout_of_lockedMessageRigidity hrigid hY α α₀ hα hα₀

/-- Appendix I.26(i)--(iii): satisfiability, sound extraction, and fixed
projection readout, omitting only the separate polynomial-uniformity item. -/
theorem semantic_i26_items_of_lockedMessageRigidity
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
  exact
    ⟨D.satOnSupport hY,
      (fun α hα => D.cnfSound hα),
      D.singleMessageReadout_of_lockedMessageRigidity hrigid hY⟩

/-- The arbitrary-output SAT-search decoder theorem follows from the actual
Appendix D.8 locked-completion rigidity plus Appendix I satisfiability. -/
theorem exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (hrigid : D.core.LockedMessageRigidity)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  rcases D.satOnSupport hY with ⟨α₀, hα₀⟩
  exact
    cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
      hα₀ (D.singleMessageReadout_of_lockedMessageRigidity hrigid hY)

end AppendixICNFReadoutData

/-- A faithful D.5-style locked core with no public message tag: there is one
public lock syntax, two quotient states, and the readout predicate accepts the
message equal to the quotient state. -/
def ambiguousAppendixDLockedCore :
    AppendixDLockedCore Unit Bool Unit Bool where
  publicLockFinite := inferInstance
  quotientFinite := inferInstance
  lockAuxFinite := inferInstance
  messageFinite := inferInstance
  support := fun _ => True
  lockPredicate := fun _ _ _ _ => True
  readPredicate := fun _ z _ M => M = z

/-- The false-message locked completion in the Appendix D countermodel. -/
def ambiguousAppendixDCompletionFalse :
    ambiguousAppendixDLockedCore.LockedCompletion () where
  quotient := false
  lockAux := ()
  message := false
  lock_ok := trivial
  read_ok := rfl

/-- The true-message locked completion in the Appendix D countermodel. -/
def ambiguousAppendixDCompletionTrue :
    ambiguousAppendixDLockedCore.LockedCompletion () where
  quotient := true
  lockAux := ()
  message := true
  lock_ok := trivial
  read_ok := rfl

/-- The countermodel satisfies Appendix D.7. -/
theorem ambiguousAppendixDLockedCore_lockSatisfiable :
    ambiguousAppendixDLockedCore.LockSatisfiable := by
  intro Y _
  cases Y
  exact ⟨ambiguousAppendixDCompletionFalse⟩

/-- The countermodel has deterministic readout for each fixed readout state. -/
theorem ambiguousAppendixDLockedCore_readDeterministic :
    ambiguousAppendixDLockedCore.ReadDeterministic := by
  intro _ _ _ _ _ hM hM'
  exact hM.trans hM'.symm

/-- D.5--D.7 plus deterministic readout do not imply D.8: the two locked
completions carry different messages. -/
theorem ambiguousAppendixDLockedCore_not_lockedMessageRigidity :
    ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity := by
  exact
    AppendixDLockedCore.not_lockedMessageRigidity_of_distinct_completions
      ambiguousAppendixDLockedCore
      (Y := ())
      trivial
      ambiguousAppendixDCompletionFalse
      ambiguousAppendixDCompletionTrue
      (by
        intro h
        cases h)

/-- Appendix D witness data built from the same ambiguous locked core and the
one-variable tautological CNF witnesses. -/
def ambiguousAppendixDWitnessData :
    AppendixDWitnessData Unit Bool Unit Bool Unit oneVarReadoutWitness where
  core := ambiguousAppendixDLockedCore
  support := fun _ => True
  publicLock := fun _ => ()
  validWitness := fun _ σ => ConcreteCNF.IsSatFormula oneVarTautologyCNF σ
  witnessMessage := fun _ σ => oneVarReadout σ
  witnessCompletion := by
    intro Y W _
    exact
      { quotient := oneVarReadout W
        lockAux := ()
        message := oneVarReadout W
        lock_ok := trivial
        read_ok := rfl }
  support_publicLock := by
    intro _ _
    trivial
  witnessMessage_eq_completionMessage := by
    intro _ _ _
    rfl

/-- The ambiguous Appendix D witness layer fails D.41's single-message promise. -/
theorem ambiguousAppendixDWitnessData_not_singleMessagePromise :
    ¬ ambiguousAppendixDWitnessData.SingleMessagePromise := by
  exact
    AppendixDWitnessData.not_singleMessagePromise_of_distinct_valid_witnessMessages
      ambiguousAppendixDWitnessData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Appendix I CNF realization data over the ambiguous Appendix D locked core. -/
def ambiguousAppendixICNFReadoutData :
    AppendixICNFReadoutData
      Unit Bool Unit Bool Unit oneVarReadoutPublicVar oneVarReadoutWitness where
  toAppendixDWitnessData := ambiguousAppendixDWitnessData
  formula := fun _ => oneVarTautologyCNF
  extract := fun _ σ => σ
  projection := fun _ σ => oneVarReadout σ
  cnfSound := by
    intro _ _ h
    exact h
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl
  satOnSupport := by
    intro _ _
    exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The ambiguous Appendix I data is satisfiable, but because D.8 fails it has
no message correct for arbitrary satisfying SAT-search outputs. -/
theorem ambiguousAppendixICNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixICNFReadoutData.formula ()))
        (ambiguousAppendixICNFReadoutData.projection ()) msg := by
  simpa [ambiguousAppendixICNFReadoutData, ambiguousAppendixDWitnessData] using
    oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs

end Mettapedia.Computability.PNP
