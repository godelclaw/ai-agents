import Mettapedia.Computability.PNP.PNPv13AppendixDProductCNFBridge

/-!
# PNP v13: exact CNF realization of Appendix D product witnesses

This file strengthens the product/CNF bridge with a semantic exactness
condition: every valid Appendix D product witness has a satisfying CNF encoding
whose fixed projection is that witness's message.

The exactness repair still does not create locked-message rigidity.  If there
are two valid product witnesses with different messages, exact CNF realization
turns them into two satisfying assignments with different fixed projections,
which rules out arbitrary-output SAT-search correctness and refutes the D.8
rigidity needed by the product route.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

/-- A product-CNF readout interface with a reverse encoding for every valid
product witness.  The reverse direction is intentionally message-level rather
than syntactic: it is the exact property needed by the SAT-search readout
argument. -/
structure AppendixDProductExactCNFReadoutData
    (PublicLock : Type u) (Quotient : Type v) (LockAux : Type w)
    (Message : Type x) (Public : Type y) (RawGauge : Type z)
    (BufferAux : Type q) (Aux : Type r) (Var : Public → Type s)
    extends AppendixDProductCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var where
  /-- Encode a semantic product witness as a CNF assignment. -/
  encode : (Y : Public) → product.Witness → ConcreteCNF.Assignment (Var Y)
  /-- Completeness direction: every valid product witness has a satisfying
  encoding. -/
  encode_satisfies :
    ∀ {Y : Public} {W : product.Witness},
      product.ValidWitness Y W →
        ConcreteCNF.IsSatFormula (formula Y) (encode Y W)
  /-- The fixed CNF projection of an encoded valid product witness is exactly
  the product witness message. -/
  projection_encode_eq_witnessMessage :
    ∀ {Y : Public} {W : product.Witness},
      product.ValidWitness Y W →
        projection Y (encode Y W) = W.message

namespace AppendixDProductExactCNFReadoutData

variable {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
variable {Message : Type x} {Public : Type y} {RawGauge : Type z}
variable {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}

/-- Exact CNF realization converts two valid product witnesses with different
messages into a failure of CNF single-message readout. -/
theorem not_singleMessageReadout_of_distinct_valid_witnessMessages
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) := by
  intro hconst
  have hsatW : ConcreteCNF.IsSatFormula (D.formula Y) (D.encode Y W) :=
    D.encode_satisfies hW
  have hsatW' : ConcreteCNF.IsSatFormula (D.formula Y) (D.encode Y W') :=
    D.encode_satisfies hW'
  have hproj : D.projection Y (D.encode Y W) =
      D.projection Y (D.encode Y W') :=
    hconst (D.encode Y W) (D.encode Y W') hsatW hsatW'
  have hmsg : W.message = W'.message :=
    (D.projection_encode_eq_witnessMessage hW).symm.trans
      (hproj.trans (D.projection_encode_eq_witnessMessage hW'))
  exact hdiff hmsg

/-- With exact CNF realization, two valid product witnesses with different
messages rule out any fixed message correct for all satisfying SAT-search
outputs. -/
theorem not_exists_correctForAllSatSearchOutputs_of_distinct_valid_witnessMessages
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg := by
  exact
    fun h =>
      D.not_singleMessageReadout_of_distinct_valid_witnessMessages hW hW' hdiff
        (cnf_singleMessageReadout_of_exists_correctForAllSatSearchOutputs h)

/-- The same pair of valid product witnesses refutes the locked-core D.8 theorem
needed by the product route. -/
theorem not_lockedMessageRigidity_of_distinct_valid_witnessMessages
    (D : AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    {Y : Public} {W W' : D.product.Witness}
    (hY : D.product.support Y)
    (hW : D.product.ValidWitness Y W)
    (hW' : D.product.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ D.product.core.LockedMessageRigidity := by
  exact
    D.product.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
      hY hW hW' hdiff

end AppendixDProductExactCNFReadoutData

/-- Every assignment satisfies the one-variable tautological CNF. -/
theorem oneVarTautologyCNF_satisfied_any
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF σ := by
  intro clause hclause
  rw [oneVarTautologyCNF] at hclause
  simp only [List.mem_singleton] at hclause
  rw [hclause]
  cases hbit : σ 0
  · exact
      ⟨ConcreteCNF.Literal.neg (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, hbit]⟩
  · exact
      ⟨ConcreteCNF.Literal.pos (0 : Fin 1), by simp,
        by simp [ConcreteCNF.Literal.eval, hbit]⟩

/-- The two explicit product countermodel witnesses have different messages. -/
theorem ambiguousAppendixDProductWitnessFalse_message_ne_true :
    ambiguousAppendixDProductWitnessFalse.message ≠
      ambiguousAppendixDProductWitnessTrue.message := by
  intro h
  have hpoint := congrFun h ()
  cases hpoint

/-- Encode a singleton-block product witness by exposing its message bit as the
one CNF variable. -/
def encodeAmbiguousAppendixDProductWitness
    (W : ambiguousAppendixDProductConstruction.Witness) :
    ConcreteCNF.Assignment (Fin 1) :=
  fun _ => W.message ()

/-- The product-CNF countermodel is exact at the message level: every valid
product witness encodes as a satisfying CNF assignment whose projection is the
witness message. -/
def ambiguousAppendixDProductExactCNFReadoutData :
    AppendixDProductExactCNFReadoutData
      Unit (Unit → Bool) (Unit → Bool) (Unit → Bool)
      Unit Unit Unit Unit oneVarReadoutPublicVar where
  toAppendixDProductCNFReadoutData := ambiguousAppendixDProductCNFReadoutData
  encode := fun _ W => encodeAmbiguousAppendixDProductWitness W
  encode_satisfies := by
    intro _ W _
    exact oneVarTautologyCNF_satisfied_any
      (encodeAmbiguousAppendixDProductWitness W)
  projection_encode_eq_witnessMessage := by
    intro _ W _
    funext u
    cases u
    rfl

/-- Exact CNF realization still does not force single-message readout in the
product countermodel. -/
theorem ambiguousAppendixDProductExactCNFReadoutData_not_singleMessageReadout :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (ambiguousAppendixDProductExactCNFReadoutData.formula ()))
      (ambiguousAppendixDProductExactCNFReadoutData.projection ()) := by
  exact
    ambiguousAppendixDProductExactCNFReadoutData
      |>.not_singleMessageReadout_of_distinct_valid_witnessMessages
        ambiguousAppendixDProductWitnessFalse_valid
        ambiguousAppendixDProductWitnessTrue_valid
        ambiguousAppendixDProductWitnessFalse_message_ne_true

/-- Exact CNF realization still has no message correct for arbitrary satisfying
SAT-search outputs in the product countermodel. -/
theorem ambiguousAppendixDProductExactCNFReadoutData_not_exists_correctForAll :
    ¬ ∃ msg : Unit → Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (ambiguousAppendixDProductExactCNFReadoutData.formula ()))
        (ambiguousAppendixDProductExactCNFReadoutData.projection ()) msg := by
  exact
    ambiguousAppendixDProductExactCNFReadoutData
      |>.not_exists_correctForAllSatSearchOutputs_of_distinct_valid_witnessMessages
        ambiguousAppendixDProductWitnessFalse_valid
        ambiguousAppendixDProductWitnessTrue_valid
        ambiguousAppendixDProductWitnessFalse_message_ne_true

/-- Exact CNF realization still does not repair the missing locked-core D.8
theorem. -/
theorem ambiguousAppendixDProductExactCNFReadoutData_not_lockedMessageRigidity :
    ¬ ambiguousAppendixDProductExactCNFReadoutData.product.core.LockedMessageRigidity := by
  exact
    ambiguousAppendixDProductExactCNFReadoutData
      |>.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
        (Y := ())
        trivial
        ambiguousAppendixDProductWitnessFalse_valid
        ambiguousAppendixDProductWitnessTrue_valid
        ambiguousAppendixDProductWitnessFalse_message_ne_true

end Mettapedia.Computability.PNP
