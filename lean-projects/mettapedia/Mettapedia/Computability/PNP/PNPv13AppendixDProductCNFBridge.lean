import Mettapedia.Computability.PNP.PNPv13AppendixDProductConstruction

/-!
# PNP v13: Appendix D product witnesses and Appendix I CNF readout

This file connects the Appendix D.36--D.41 product witness relation to the
Appendix I.23--I.26 CNF readout layer.  It tests the concrete repair route in
which the product construction, rather than an abstract witness relation, is
supposed to supply the SAT-search single-message theorem.

The bridge is sharp: locked-message rigidity of the underlying locked core
does imply CNF-level readout constancy for product witnesses, but two satisfying
CNF assignments whose extracted product witnesses carry different messages
refute that same locked-core rigidity.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

/-- Appendix I readout data specialized to the Appendix D product witness
relation.  The formula, extraction map, and fixed projection are the semantic
parts of Appendix I.23--I.26; polynomial-time and size bounds are deliberately
outside this local message-constancy argument. -/
structure AppendixDProductCNFReadoutData
    (PublicLock : Type u) (Quotient : Type v) (LockAux : Type w)
    (Message : Type x) (Public : Type y) (RawGauge : Type z)
    (BufferAux : Type q) (Aux : Type r) (Var : Public → Type s) where
  product :
    AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux
  formula : (Y : Public) → ConcreteCNF.Formula (Var Y)
  extract : (Y : Public) → ConcreteCNF.Assignment (Var Y) → product.Witness
  projection : (Y : Public) → ConcreteCNF.Assignment (Var Y) → Message
  /-- CNF soundness for the product witness relation. -/
  cnfSound :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        product.ValidWitness Y (extract Y α)
  /-- The fixed CNF projection reads exactly the product witness message on
  satisfying assignments. -/
  projection_eq_witnessMessage :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        projection Y α = (extract Y α).message
  satOnSupport :
    ∀ {Y : Public}, product.support Y → ∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (formula Y) α

namespace AppendixDProductCNFReadoutData

variable {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
variable {Message : Type x} {Public : Type y} {RawGauge : Type z}
variable {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}

/-- Appendix I.23/I.25 in the product-witness specialization: D.8 for the
underlying locked core gives CNF-level single-message readout. -/
theorem singleMessageReadout_of_lockedMessageRigidity
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  intro α β hα hβ
  calc
    D.projection Y α = (D.extract Y α).message :=
      D.projection_eq_witnessMessage hα
    _ = (D.extract Y β).message :=
      D.product.singleMessagePromise_of_lockedMessageRigidity
        hrigid hY (D.cnfSound hα) (D.cnfSound hβ)
    _ = D.projection Y β :=
      (D.projection_eq_witnessMessage hβ).symm

/-- Appendix I.24/I.25, proposition-level form for product witnesses. -/
def ProjectedMessageSpec
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (Y : Public) (msg : Message) : Prop :=
  ∀ {α : ConcreteCNF.Assignment (Var Y)},
    ConcreteCNF.IsSatFormula (D.formula Y) α →
      D.projection Y α = msg

/-- Under locked-message rigidity there is a single projected message for each
supported product public instance. -/
theorem exists_projectedMessageSpec_of_lockedMessageRigidity
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    ∃ msg : Message, D.ProjectedMessageSpec Y msg := by
  rcases D.satOnSupport hY with ⟨α₀, hα₀⟩
  refine ⟨D.projection Y α₀, ?_⟩
  intro α hα
  exact D.singleMessageReadout_of_lockedMessageRigidity hrigid hY α α₀ hα hα₀

/-- Product-witness version of Appendix I.26(i)--(iii), omitting only the
separate polynomial-uniformity clause. -/
theorem semantic_i26_items_of_lockedMessageRigidity
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    (∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α) ∧
    (∀ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α →
        D.product.ValidWitness Y (D.extract Y α)) ∧
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  exact
    ⟨D.satOnSupport hY,
      (fun α hα => D.cnfSound hα),
      D.singleMessageReadout_of_lockedMessageRigidity hrigid hY⟩

/-- The arbitrary-output SAT-search decoder theorem follows for product
witnesses from locked-message rigidity plus Appendix I satisfiability. -/
theorem exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  rcases D.satOnSupport hY with ⟨α₀, hα₀⟩
  exact
    cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
      hα₀ (D.singleMessageReadout_of_lockedMessageRigidity hrigid hY)

/-- Exact product-CNF obstruction: if two satisfying CNF assignments have
different fixed projections, then the underlying locked core cannot satisfy
Appendix D.8. -/
theorem not_lockedMessageRigidity_of_distinct_satisfying_projections
    (D : AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {α β : ConcreteCNF.Assignment (Var Y)}
    (hY : D.product.support Y)
    (hα : ConcreteCNF.IsSatFormula (D.formula Y) α)
    (hβ : ConcreteCNF.IsSatFormula (D.formula Y) β)
    (hdiff : D.projection Y α ≠ D.projection Y β) :
    ¬ D.product.core.LockedMessageRigidity := by
  intro hrigid
  exact hdiff
    (D.singleMessageReadout_of_lockedMessageRigidity hrigid hY α β hα hβ)

end AppendixDProductCNFReadoutData

/-- The singleton-block readout induced by the one-variable CNF assignment. -/
def oneVarSingletonBlockReadout
    (σ : ConcreteCNF.Assignment (Fin 1)) : Unit → Bool :=
  singletonBoolBlock (oneVarReadout σ)

/-- The one-variable false and true assignments have different singleton-block
product messages. -/
theorem oneVarSingletonBlockReadout_false_ne_true :
    oneVarSingletonBlockReadout oneVarFalseAssignment ≠
      oneVarSingletonBlockReadout oneVarTrueAssignment := by
  intro h
  have hpoint := congrFun h ()
  cases hpoint

/-- Extract the product witness whose quotient and message blocks both expose
the one-variable CNF readout. -/
def ambiguousAppendixDProductWitnessOfAssignment
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    ambiguousAppendixDProductConstruction.Witness where
  rawGauge := ()
  quotient := oneVarSingletonBlockReadout σ
  lockAux := singletonBoolBlock false
  bufferAux := ()
  aux := ()
  message := oneVarSingletonBlockReadout σ

/-- Every one-variable assignment extracts to a valid product witness; the CNF
satisfaction hypothesis is not needed because the product ambiguity sits in the
unconstrained quotient/message readout. -/
theorem ambiguousAppendixDProductWitnessOfAssignment_valid
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      (ambiguousAppendixDProductWitnessOfAssignment σ) := by
  refine ⟨?_, ?_, trivial, trivial, trivial⟩
  · intro C hC
    cases hC
  · intro C hC
    simp [
      ambiguousAppendixDProductConstruction,
      ambiguousPublicSyntaxDisciplinedLocalCore,
      ambiguousAppendixDLocalBoolLockedCore,
      oneBitReadEqualsQuotientPredicate] at hC
    subst C
    simp [
      ambiguousAppendixDProductWitnessOfAssignment,
      oneVarSingletonBlockReadout,
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble,
      singletonBoolBlock]

/-- Appendix I CNF readout data over the actual Appendix D product witness
relation, instantiated by the one-variable tautological CNF. -/
def ambiguousAppendixDProductCNFReadoutData :
    AppendixDProductCNFReadoutData
      Unit (Unit → Bool) (Unit → Bool) (Unit → Bool)
      Unit Unit Unit Unit oneVarReadoutPublicVar where
  product := ambiguousAppendixDProductConstruction
  formula := fun _ => oneVarTautologyCNF
  extract := fun _ σ => ambiguousAppendixDProductWitnessOfAssignment σ
  projection := fun _ σ => oneVarSingletonBlockReadout σ
  cnfSound := by
    intro _ σ _
    exact ambiguousAppendixDProductWitnessOfAssignment_valid σ
  projection_eq_witnessMessage := by
    intro _ _ _
    rfl
  satOnSupport := by
    intro _ _
    exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩

/-- The product-CNF countermodel refutes Appendix D.8 for the underlying locked
core using two satisfying CNF assignments with different product messages. -/
theorem ambiguousAppendixDProductCNFReadoutData_not_lockedMessageRigidity :
    ¬ ambiguousAppendixDProductCNFReadoutData.product.core.LockedMessageRigidity := by
  exact
    ambiguousAppendixDProductCNFReadoutData
      |>.not_lockedMessageRigidity_of_distinct_satisfying_projections
        (Y := ())
        (α := oneVarFalseAssignment)
        (β := oneVarTrueAssignment)
        trivial
        oneVarTautologyCNF_satisfied_false
        oneVarTautologyCNF_satisfied_true
        oneVarSingletonBlockReadout_false_ne_true

/-- Consequently the product-CNF countermodel has no fixed message correct for
all arbitrary satisfying SAT-search outputs. -/
theorem ambiguousAppendixDProductCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Unit → Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixDProductCNFReadoutData.formula ()))
        (ambiguousAppendixDProductCNFReadoutData.projection ()) msg := by
  exact
    not_exists_correctForAllSatSearchOutputs_of_distinct_satisfying_readouts
      (sat := ConcreteCNF.IsSatFormula
        (ambiguousAppendixDProductCNFReadoutData.formula ()))
      (readout := ambiguousAppendixDProductCNFReadoutData.projection ())
      (w₁ := oneVarFalseAssignment)
      (w₂ := oneVarTrueAssignment)
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarSingletonBlockReadout_false_ne_true

end Mettapedia.Computability.PNP
