import Mettapedia.Computability.PNP.PNPv13ConcreteSATReadoutObstruction

/-!
# PNP v13: manuscript-shaped CNF readout constancy

This file formalizes the exact readout-constancy bridge used in v13,
Appendix I.4.  The manuscript proves CNF-level constancy from three ingredients:

* every satisfying CNF assignment extracts to a valid witness;
* the fixed CNF projection reads the same message as the extracted witness;
* valid witnesses for a supported public instance satisfy the single-message
  promise.

The last ingredient is not a consequence of CNF compilation alone.  A concrete
one-variable countermodel at the end satisfies the extraction/projection
interface while failing the single-message promise and arbitrary-output SAT
search correctness.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z

/-- The manuscript-shaped interface behind v13 Appendix I.19--I.23.

For each public instance `Y`, `formula Y` is the CNF `F_Y`, `extract Y`
is `Wit_Y`, and `projection Y` is the fixed message projection `π_M`.
The fields keep only the hypotheses needed to prove CNF-level readout
constancy; uniformity, polynomial size, and clock bounds live outside this
local constancy argument. -/
structure ManuscriptCNFReadoutData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (Message : Type z) where
  /-- Public instances on which the manuscript ensemble promises a message. -/
  support : Public → Prop
  /-- The concrete CNF `F_Y`. -/
  formula : (Y : Public) → ConcreteCNF.Formula (Var Y)
  /-- The semantic witness relation `R(Y,W)=1`. -/
  validWitness : (Y : Public) → Witness Y → Prop
  /-- The witness extraction map `Wit_Y(α)` from CNF assignments. -/
  extract : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Witness Y
  /-- The semantic message coordinate `M(W)`. -/
  witnessMessage : (Y : Public) → Witness Y → Message
  /-- The fixed CNF-level message projection `π_M(α)`. -/
  projection : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Message
  /-- Proposition I.19, forward direction: satisfying CNF assignments extract
  to valid semantic witnesses. -/
  cnfSound :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        validWitness Y (extract Y α)
  /-- Definition I.18 compatibility: the extracted witness message is exactly
  the fixed CNF projection on satisfying assignments. -/
  projection_eq_witnessMessage :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        projection Y α = witnessMessage Y (extract Y α)

namespace ManuscriptCNFReadoutData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {Message : Type z}

/-- The v13 single-message promise, restricted to supported public instances:
any two valid witnesses carry the same semantic message. -/
def SingleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public} {W W' : Witness Y},
    D.support Y →
      D.validWitness Y W →
        D.validWitness Y W' →
          D.witnessMessage Y W = D.witnessMessage Y W'

/-- Every valid semantic witness over a supported public instance is
represented by some satisfying CNF assignment.  This is the completeness
direction needed to turn CNF-level SAT-search correctness back into the
semantic single-message promise. -/
def CNFExtractionComplete
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public} {W : Witness Y},
    D.support Y →
      D.validWitness Y W →
        ∃ α : ConcreteCNF.Assignment (Var Y),
          ConcreteCNF.IsSatFormula (D.formula Y) α ∧ D.extract Y α = W

/-- Every supported public instance has at least one satisfying CNF assignment.
This is the satisfiability side needed for the forward arbitrary-output
SAT-search decoder theorem. -/
def SupportedCNFSatisfiable
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public},
    D.support Y →
      ∃ α : ConcreteCNF.Assignment (Var Y),
        ConcreteCNF.IsSatFormula (D.formula Y) α

/-- The supported arbitrary-output SAT-search decoder obligation: for every
supported public instance, there is a message correct for every satisfying
CNF assignment that SAT search may return. -/
def SupportedArbitraryOutputSATSearchCorrect
    (D : ManuscriptCNFReadoutData Public Var Witness Message) : Prop :=
  ∀ {Y : Public},
    D.support Y →
      ∃ msg : Message,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg

/-- Lemma I.23 in the manuscript-shaped interface: the witness-level
single-message promise implies CNF-level readout constancy for the fixed
projection. -/
theorem singleMessageReadout_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  intro α β hα hβ
  calc
    D.projection Y α = D.witnessMessage Y (D.extract Y α) :=
      D.projection_eq_witnessMessage hα
    _ = D.witnessMessage Y (D.extract Y β) :=
      hpromise hY (D.cnfSound hα) (D.cnfSound hβ)
    _ = D.projection Y β :=
      (D.projection_eq_witnessMessage hβ).symm

/-- The arbitrary-output SAT-search decoder obligation closes once the
manuscript-shaped CNF is satisfiable and satisfies the single-message promise. -/
theorem exists_correctForAllSatSearchOutputs_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
      hα₀ (D.singleMessageReadout_of_singleMessagePromise hpromise hY)

/-- Supported form of the forward bridge: the single-message promise plus
supported satisfiability supplies a message correct for every satisfying
SAT-search output on each supported public instance. -/
theorem supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hpromise : D.SingleMessagePromise)
    (hsat : D.SupportedCNFSatisfiable) :
    D.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y hY
  rcases hsat hY with ⟨α₀, hα₀⟩
  exact D.exists_correctForAllSatSearchOutputs_of_singleMessagePromise hpromise hY hα₀

/-- Converse bridge: if every valid witness is represented by a satisfying
assignment, then arbitrary-output SAT-search correctness on supported public
instances forces the semantic single-message promise.  Thus SAT search
correctness cannot replace the manuscript's single-message theorem; under the
natural completeness direction it is at least as strong. -/
theorem singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    (hcorrect : D.SupportedArbitraryOutputSATSearchCorrect) :
    D.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  rcases hcomplete hY hW with ⟨α, hα, hextract⟩
  rcases hcomplete hY hW' with ⟨β, hβ, hextract'⟩
  rcases hcorrect hY with ⟨msg, hmsg⟩
  have hproj :
      D.projection Y α = D.witnessMessage Y W := by
    simpa [hextract] using D.projection_eq_witnessMessage hα
  have hproj' :
      D.projection Y β = D.witnessMessage Y W' := by
    simpa [hextract'] using D.projection_eq_witnessMessage hβ
  calc
    D.witnessMessage Y W = D.projection Y α := hproj.symm
    _ = msg := hmsg ⟨α, hα⟩
    _ = D.projection Y β := (hmsg ⟨β, hβ⟩).symm
    _ = D.witnessMessage Y W' := hproj'

/-- Under supported satisfiability and CNF extraction completeness,
arbitrary-output SAT-search correctness is equivalent to the semantic
single-message promise.  This is the minimal repair target for the v13 CNF
readout route. -/
theorem supportedArbitraryOutputSATSearchCorrect_iff_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  constructor
  · intro hcorrect
    exact
      D.singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
        hcomplete hcorrect
  · intro hpromise
    exact D.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise hpromise hsat

/-- If CNF extraction is complete, failure of the semantic single-message
promise rules out the supported arbitrary-output SAT-search decoder theorem. -/
theorem not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    (hnot : ¬ D.SingleMessagePromise) :
    ¬ D.SupportedArbitraryOutputSATSearchCorrect := by
  intro hcorrect
  exact hnot
    (D.singleMessagePromise_of_cnfExtractionComplete_of_supportedArbitraryOutputSATSearchCorrect
      hcomplete hcorrect)

/-- Exact obstruction to the v13 witness-level single-message promise:
two valid witnesses over one supported public input with different semantic
messages refute the promise. -/
theorem not_singleMessagePromise_of_distinct_valid_witnessMessages
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SingleMessagePromise := by
  intro hpromise
  exact hdiff (hpromise hY hW hW')

/-- Complete-CNF form of the readout blocker: once every valid witness is
represented by a satisfying assignment, two valid witnesses with distinct
messages rule out arbitrary-output SAT-search correctness on supported
instances. -/
theorem not_supportedArbitraryOutputSATSearchCorrect_of_complete_distinct_valid_witnessMessages
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hcomplete : D.CNFExtractionComplete)
    {Y : Public} {W W' : Witness Y}
    (hY : D.support Y)
    (hW : D.validWitness Y W) (hW' : D.validWitness Y W')
    (hdiff : D.witnessMessage Y W ≠ D.witnessMessage Y W') :
    ¬ D.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    D.not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
      hcomplete
      (D.not_singleMessagePromise_of_distinct_valid_witnessMessages
        hY hW hW' hdiff)

end ManuscriptCNFReadoutData

/-- A refinement of `ManuscriptCNFReadoutData` that exposes exactly the
locked-layer data used in v13 Proposition 4.10.  A valid witness has a
locked-layer view, the locked layer accepts that view, and the witness message
is the message read from that view. -/
structure LockedLayerCNFReadoutData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (LockView : Public → Type x) (Message : Type z) extends
    ManuscriptCNFReadoutData Public Var Witness Message where
  /-- The locked-layer coordinates `(z, ξ_lock, M)` extracted from a witness. -/
  lockView : (Y : Public) → Witness Y → LockView Y
  /-- The locked-layer predicate `Lock_Y(z, ξ_lock, M)=1`. -/
  lockAccept : (Y : Public) → LockView Y → Prop
  /-- The message coordinate carried by a locked-layer view. -/
  lockMessage : (Y : Public) → LockView Y → Message
  /-- Definition 4.8, locked-layer clause: every valid witness satisfies the
  locked layer. -/
  validWitness_lockAccept :
    ∀ {Y : Public} {W : Witness Y},
      validWitness Y W → lockAccept Y (lockView Y W)
  /-- The semantic witness message is the message coordinate in its locked view. -/
  witnessMessage_eq_lockMessage :
    ∀ {Y : Public} {W : Witness Y},
      validWitness Y W → witnessMessage Y W = lockMessage Y (lockView Y W)

namespace LockedLayerCNFReadoutData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {LockView : Public → Type x}
variable {Message : Type z}

/-- Hypothesis 4.9: accepted locked-layer views over a supported public input
all carry the same message. -/
def LockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message) : Prop :=
  ∀ {Y : Public} {L L' : LockView Y},
    D.support Y →
      D.lockAccept Y L →
        D.lockAccept Y L' →
          D.lockMessage Y L = D.lockMessage Y L'

/-- Proposition 4.10 in the locked-layer interface: locked-layer rigidity
implies the witness-level single-message promise. -/
theorem singleMessagePromise_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity) :
    D.toManuscriptCNFReadoutData.SingleMessagePromise := by
  intro Y W W' hY hW hW'
  calc
    D.witnessMessage Y W = D.lockMessage Y (D.lockView Y W) :=
      D.witnessMessage_eq_lockMessage hW
    _ = D.lockMessage Y (D.lockView Y W') :=
      hrigid hY (D.validWitness_lockAccept hW) (D.validWitness_lockAccept hW')
    _ = D.witnessMessage Y W' :=
      (D.witnessMessage_eq_lockMessage hW').symm

/-- Combining Proposition 4.10 with Appendix I.23: locked-layer rigidity
implies CNF-level readout constancy for the fixed message projection. -/
theorem singleMessageReadout_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact
    D.toManuscriptCNFReadoutData.singleMessageReadout_of_singleMessagePromise
      (D.singleMessagePromise_of_lockedLayerRigidity hrigid) hY

/-- The arbitrary-output SAT-search decoder obligation closes from
locked-layer rigidity plus one satisfying CNF assignment. -/
theorem exists_correctForAllSatSearchOutputs_of_lockedLayerRigidity
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    (hrigid : D.LockedLayerRigidity)
    {Y : Public} (hY : D.support Y)
    {α₀ : ConcreteCNF.Assignment (Var Y)}
    (hα₀ : ConcreteCNF.IsSatFormula (D.formula Y) α₀) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    D.toManuscriptCNFReadoutData.exists_correctForAllSatSearchOutputs_of_singleMessagePromise
      (D.singleMessagePromise_of_lockedLayerRigidity hrigid) hY hα₀

/-- Exact obstruction to Hypothesis 4.9: two accepted locked-layer views over
one supported public input with different message coordinates refute
locked-layer rigidity. -/
theorem not_lockedLayerRigidity_of_distinct_accepted_lockMessages
    (D : LockedLayerCNFReadoutData Public Var Witness LockView Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.lockMessage Y L ≠ D.lockMessage Y L') :
    ¬ D.LockedLayerRigidity := by
  intro hrigid
  exact hdiff (hrigid hY hL hL')

end LockedLayerCNFReadoutData

/-- A refinement that exposes the manuscript's deterministic readout predicate
`Read_Y(z, ξ_lock, M)`.  Determinism says a fixed readout state has at most one
message, but this is weaker than locked-layer rigidity unless all accepted
locked views are forced into a message-compatible readout state. -/
structure DeterministicReadoutLockedLayerData (Public : Type u)
    (Var : Public → Type v) (Witness : Public → Type w)
    (LockView : Public → Type x) (ReadState : Public → Type y)
    (Message : Type z) extends
    LockedLayerCNFReadoutData Public Var Witness LockView Message where
  /-- The part of `(z, ξ_lock)` seen by the deterministic readout predicate. -/
  readState : (Y : Public) → LockView Y → ReadState Y
  /-- The readout predicate `Read_Y(state,M)=1`. -/
  readAccept : (Y : Public) → ReadState Y → Message → Prop
  /-- Accepted locked views satisfy the deterministic readout predicate for
  their own message. -/
  lockAccept_readAccept :
    ∀ {Y : Public} {L : LockView Y},
      lockAccept Y L → readAccept Y (readState Y L) (lockMessage Y L)
  /-- Determinism of `Read_Y`: for a fixed readout state, at most one message
  is accepted. -/
  readAccept_deterministic :
    ∀ {Y : Public} {state : ReadState Y} {M M' : Message},
      readAccept Y state M → readAccept Y state M' → M = M'

namespace DeterministicReadoutLockedLayerData

variable {Public : Type u} {Var : Public → Type v}
variable {Witness : Public → Type w} {LockView : Public → Type x}
variable {ReadState : Public → Type y} {Message : Type z}

/-- A sufficient condition turning deterministic readout into locked-layer
rigidity: accepted locked views over the same supported public input have the
same readout state. -/
def AcceptedReadStateConstancy
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message) : Prop :=
  ∀ {Y : Public} {L L' : LockView Y},
    D.support Y →
      D.lockAccept Y L →
        D.lockAccept Y L' →
          D.readState Y L = D.readState Y L'

/-- Deterministic readout plus accepted-state constancy implies Hypothesis 4.9
locked-layer rigidity. -/
theorem lockedLayerRigidity_of_acceptedReadStateConstancy
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    (hstate : D.AcceptedReadStateConstancy) :
    D.toLockedLayerCNFReadoutData.LockedLayerRigidity := by
  intro Y L L' hY hL hL'
  have hs : D.readState Y L = D.readState Y L' :=
    hstate hY hL hL'
  have hreadL : D.readAccept Y (D.readState Y L) (D.lockMessage Y L) :=
    D.lockAccept_readAccept hL
  have hreadL' : D.readAccept Y (D.readState Y L') (D.lockMessage Y L') :=
    D.lockAccept_readAccept hL'
  rw [← hs] at hreadL'
  exact D.readAccept_deterministic hreadL hreadL'

/-- Deterministic readout closes the SAT-search readout route only with the
extra accepted-state constancy premise. -/
theorem exists_correctForAllSatSearchOutputs_of_acceptedReadStateConstancy
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
    D.toLockedLayerCNFReadoutData.exists_correctForAllSatSearchOutputs_of_lockedLayerRigidity
      (D.lockedLayerRigidity_of_acceptedReadStateConstancy hstate) hY hα₀

/-- Exact obstruction to the extra state-constancy premise: deterministic
readout is compatible with several accepted readout states, and two such
states already refute accepted-state constancy. -/
theorem not_acceptedReadStateConstancy_of_distinct_accepted_readStates
    (D : DeterministicReadoutLockedLayerData
      Public Var Witness LockView ReadState Message)
    {Y : Public} {L L' : LockView Y}
    (hY : D.support Y)
    (hL : D.lockAccept Y L) (hL' : D.lockAccept Y L')
    (hdiff : D.readState Y L ≠ D.readState Y L') :
    ¬ D.AcceptedReadStateConstancy := by
  intro hstate
  exact hdiff (hstate hY hL hL')

end DeterministicReadoutLockedLayerData

/-- A single supported public instance used to stress-test the interface without
the witness-level single-message promise. -/
def oneVarReadoutPublicVar (_ : Unit) : Type :=
  Fin 1

/-- In this countermodel, a semantic witness is just the CNF assignment read
through the intended witness blocks. -/
def oneVarReadoutWitness (_ : Unit) : Type :=
  ConcreteCNF.Assignment (Fin 1)

/-- In the locked-layer countermodel, the locked view is just the same free CNF
assignment. -/
def oneVarReadoutLockView (_ : Unit) : Type :=
  ConcreteCNF.Assignment (Fin 1)

/-- The readout state in the deterministic-readout countermodel is the state
whose unique message is its Boolean value. -/
def oneVarReadoutReadState (_ : Unit) : Type :=
  Bool

/-- The compiler/extraction/projection shape alone can be satisfied by a CNF
whose free satisfying assignments have different projected messages. -/
def ambiguousOneVarManuscriptCNFReadoutData :
    ManuscriptCNFReadoutData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness Bool where
  support := fun _ => True
  formula := fun _ => oneVarTautologyCNF
  validWitness := fun _ σ => ConcreteCNF.IsSatFormula oneVarTautologyCNF σ
  extract := fun _ σ => σ
  witnessMessage := fun _ σ => oneVarReadout σ
  projection := fun _ σ => oneVarReadout σ
  cnfSound := by
    intro _ _ h
    exact h
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl

/-- The countermodel public instance is in support. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_support :
    ambiguousOneVarManuscriptCNFReadoutData.support () := by
  trivial

/-- The countermodel CNF is satisfiable. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_satisfiable :
    ∃ α : ConcreteCNF.Assignment (oneVarReadoutPublicVar ()),
      ConcreteCNF.IsSatFormula
        (ambiguousOneVarManuscriptCNFReadoutData.formula ()) α := by
  exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The countermodel is supported-satisfiable in the manuscript-shaped
interface. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable :
    ambiguousOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y _hY
  cases Y
  exact ambiguousOneVarManuscriptCNFReadoutData_satisfiable

/-- The countermodel also satisfies the natural extraction-completeness
direction: every valid witness is already a satisfying CNF assignment and is
extracted by the identity map. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_cnfExtractionComplete :
    ambiguousOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  intro Y W _hY hW
  cases Y
  exact ⟨W, hW, rfl⟩

/-- Without the single-message promise, the manuscript-shaped compiler
interface permits two valid witnesses with different messages. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_singleMessagePromise :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ManuscriptCNFReadoutData.not_singleMessagePromise_of_distinct_valid_witnessMessages
      ambiguousOneVarManuscriptCNFReadoutData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Consequently the compiler/extraction/projection interface alone does not
give the arbitrary-output SAT-search decoder theorem. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarManuscriptCNFReadoutData.formula ()))
        (ambiguousOneVarManuscriptCNFReadoutData.projection ()) msg := by
  simpa [ambiguousOneVarManuscriptCNFReadoutData] using
    oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs

/-- Complete extraction plus the two-message ambiguity rules out the supported
arbitrary-output SAT-search obligation globally, not merely at a hand-selected
message. -/
theorem ambiguousOneVarManuscriptCNFReadoutData_not_supportedArbitraryOutputSATSearchCorrect :
    ¬ ambiguousOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  exact
    ManuscriptCNFReadoutData.not_supportedArbitraryOutputSATSearchCorrect_of_cnfExtractionComplete_of_not_singleMessagePromise
      ambiguousOneVarManuscriptCNFReadoutData
      ambiguousOneVarManuscriptCNFReadoutData_cnfExtractionComplete
      ambiguousOneVarManuscriptCNFReadoutData_not_singleMessagePromise

/-- A semantic witness type used to test whether CNF-side readout constancy can
replace extraction completeness.  The CNF below only extracts the `false`
witness, while `true` remains a valid unrepresented semantic witness. -/
def unrepresentedOneVarReadoutWitness (_ : Unit) : Type :=
  Bool

/-- CNF-side SAT-search correctness can hold vacuously on the extracted image
while the semantic witness relation is still ambiguous.  This is not a complete
CNF realization; it marks why `CNFExtractionComplete` is a real premise in the
converse bridge above. -/
def unrepresentedOneVarManuscriptCNFReadoutData :
    ManuscriptCNFReadoutData
      Unit oneVarReadoutPublicVar unrepresentedOneVarReadoutWitness Bool where
  support := fun _ => True
  formula := fun _ => oneVarTautologyCNF
  validWitness := fun _ _ => True
  extract := fun _ _ => false
  witnessMessage := fun _ W => W
  projection := fun _ _ => false
  cnfSound := by
    intro _ _ _
    trivial
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl

/-- The unrepresented-witness countermodel is supported-satisfiable. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_supportedCNFSatisfiable :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedCNFSatisfiable := by
  intro Y _hY
  cases Y
  exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The CNF projection in the unrepresented-witness countermodel is constant
on all satisfying assignments. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_singleMessageReadout :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (unrepresentedOneVarManuscriptCNFReadoutData.formula ()))
      (unrepresentedOneVarManuscriptCNFReadoutData.projection ()) := by
  intro _ _ _ _
  rfl

/-- Hence the supported arbitrary-output SAT-search obligation holds on the
CNF side. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y _hY
  cases Y
  exact
    ⟨false, by
      intro _out
      rfl⟩

/-- But the semantic witness relation still has two valid witnesses with
different messages. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ManuscriptCNFReadoutData.not_singleMessagePromise_of_distinct_valid_witnessMessages
      unrepresentedOneVarManuscriptCNFReadoutData
      (Y := ())
      (W := false)
      (W' := true)
      trivial
      trivial
      trivial
      (by simp [unrepresentedOneVarManuscriptCNFReadoutData])

/-- The missing hypothesis is exactly extraction completeness: the valid `true`
witness is not the extraction of any satisfying assignment. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_not_cnfExtractionComplete :
    ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  intro hcomplete
  rcases hcomplete (Y := ()) (W := true) trivial trivial with
    ⟨α, _hα, hextract⟩
  simp [unrepresentedOneVarManuscriptCNFReadoutData] at hextract

/-- Boundary theorem: without extraction completeness, supported
arbitrary-output SAT-search correctness over the CNF can coexist with failure
of the semantic single-message promise. -/
theorem unrepresentedOneVarManuscriptCNFReadoutData_satSearchCorrect_and_not_singleMessagePromise :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise := by
  exact
    ⟨unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect,
      unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise⟩

/-- The same ambiguity satisfies the locked-layer shape if the locked layer is
not rigid: its accepted views are precisely the satisfying assignments, and
their messages are the projected variable. -/
def ambiguousOneVarLockedLayerCNFReadoutData :
    LockedLayerCNFReadoutData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness oneVarReadoutLockView Bool where
  toManuscriptCNFReadoutData := ambiguousOneVarManuscriptCNFReadoutData
  lockView := fun _ σ => σ
  lockAccept := fun _ σ => ConcreteCNF.IsSatFormula oneVarTautologyCNF σ
  lockMessage := fun _ σ => oneVarReadout σ
  validWitness_lockAccept := by
    intro _ _ h
    exact h
  witnessMessage_eq_lockMessage := by
    intro _ _ _
    rfl

/-- Without locked-layer rigidity, the locked-layer-shaped interface itself can
still have two accepted lock views with different messages. -/
theorem ambiguousOneVarLockedLayerCNFReadoutData_not_lockedLayerRigidity :
    ¬ ambiguousOneVarLockedLayerCNFReadoutData.LockedLayerRigidity := by
  exact
    LockedLayerCNFReadoutData.not_lockedLayerRigidity_of_distinct_accepted_lockMessages
      ambiguousOneVarLockedLayerCNFReadoutData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- The locked-layer-shaped countermodel inherits the same failure of
arbitrary-output SAT-search correctness. -/
theorem ambiguousOneVarLockedLayerCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarLockedLayerCNFReadoutData.formula ()))
        (ambiguousOneVarLockedLayerCNFReadoutData.projection ()) msg := by
  simpa [ambiguousOneVarLockedLayerCNFReadoutData] using
    ambiguousOneVarManuscriptCNFReadoutData_not_exists_correctForAll

/-- This model satisfies deterministic readout: each Boolean readout state
accepts exactly its own Boolean message.  It still has two accepted states. -/
def ambiguousOneVarDeterministicReadoutLockedLayerData :
    DeterministicReadoutLockedLayerData
      Unit oneVarReadoutPublicVar oneVarReadoutWitness oneVarReadoutLockView
      oneVarReadoutReadState Bool where
  toLockedLayerCNFReadoutData := ambiguousOneVarLockedLayerCNFReadoutData
  readState := fun _ σ => oneVarReadout σ
  readAccept := fun _ state msg => msg = state
  lockAccept_readAccept := by
    intro _ _ _
    rfl
  readAccept_deterministic := by
    intro _ state M M' hM hM'
    exact hM.trans hM'.symm

/-- Deterministic readout alone does not force all accepted locked views into
the same readout state. -/
theorem ambiguousOneVarDeterministicReadoutLockedLayerData_not_acceptedReadStateConstancy :
    ¬ ambiguousOneVarDeterministicReadoutLockedLayerData.AcceptedReadStateConstancy := by
  exact
    DeterministicReadoutLockedLayerData.not_acceptedReadStateConstancy_of_distinct_accepted_readStates
      ambiguousOneVarDeterministicReadoutLockedLayerData
      (Y := ())
      trivial
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Even with deterministic readout, the nonconstant one-variable model has no
message correct for arbitrary satisfying SAT-search outputs. -/
theorem ambiguousOneVarDeterministicReadoutLockedLayerData_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousOneVarDeterministicReadoutLockedLayerData.formula ()))
        (ambiguousOneVarDeterministicReadoutLockedLayerData.projection ()) msg := by
  simpa [ambiguousOneVarDeterministicReadoutLockedLayerData] using
    ambiguousOneVarLockedLayerCNFReadoutData_not_exists_correctForAll

end Mettapedia.Computability.PNP
