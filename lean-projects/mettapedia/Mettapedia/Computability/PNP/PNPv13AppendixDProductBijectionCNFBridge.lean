import Mettapedia.Computability.PNP.PNPv13AppendixDProductExactCNFBridge

/-!
# PNP v13: bijective CNF realization of Appendix D product witnesses

This file tests the strongest natural CNF-realization repair at the Appendix D
product layer: satisfying CNF assignments and valid product witnesses round-trip
through extraction and encoding.

The result is an equivalence.  Under an exact realization, CNF readout constancy
is exactly single-message constancy for valid product witnesses.  Adding
round-trip bijectivity does not create that constancy; it only prevents blaming
the compiler for losing witnesses.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

/-- Exact product-CNF readout data with round-trip laws between satisfying CNF
assignments and valid product witnesses. -/
structure AppendixDProductBijectionCNFReadoutData
    (PublicLock : Type u) (Quotient : Type v) (LockAux : Type w)
    (Message : Type x) (Public : Type y) (RawGauge : Type z)
    (BufferAux : Type q) (Aux : Type r) (Var : Public → Type s)
    extends AppendixDProductExactCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var where
  /-- Encoding then extracting a valid product witness returns the witness. -/
  extract_encode :
    ∀ {Y : Public} {W : product.Witness},
      product.ValidWitness Y W →
        extract Y (encode Y W) = W
  /-- Extracting then encoding a satisfying CNF assignment returns the
  assignment. -/
  encode_extract :
    ∀ {Y : Public} {α : ConcreteCNF.Assignment (Var Y)},
      ConcreteCNF.IsSatFormula (formula Y) α →
        encode Y (extract Y α) = α

namespace AppendixDProductBijectionCNFReadoutData

variable {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
variable {Message : Type x} {Public : Type y} {RawGauge : Type z}
variable {BufferAux : Type q} {Aux : Type r} {Var : Public → Type s}

/-- Product-witness single-message constancy for a fixed public instance. -/
def ValidProductWitnessSingleMessage
    (D : AppendixDProductBijectionCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (Y : Public) : Prop :=
  ∀ W W' : D.product.Witness,
    D.product.ValidWitness Y W →
      D.product.ValidWitness Y W' →
        W.message = W'.message

/-- In an exact product-CNF realization, CNF readout constancy is equivalent to
single-message constancy of valid product witnesses.  The round-trip fields are
not needed for the proof; their presence rules out the stronger repair claim
that bijectivity itself supplies the missing message theorem. -/
theorem singleMessageReadout_iff_validProductWitnessSingleMessage
    (D : AppendixDProductBijectionCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (Y : Public) :
    SingleMessageReadout
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) ↔
      D.ValidProductWitnessSingleMessage Y := by
  constructor
  · intro hconst W W' hW hW'
    have hsatW : ConcreteCNF.IsSatFormula (D.formula Y) (D.encode Y W) :=
      D.encode_satisfies hW
    have hsatW' : ConcreteCNF.IsSatFormula (D.formula Y) (D.encode Y W') :=
      D.encode_satisfies hW'
    have hproj : D.projection Y (D.encode Y W) =
        D.projection Y (D.encode Y W') :=
      hconst (D.encode Y W) (D.encode Y W') hsatW hsatW'
    exact
      (D.projection_encode_eq_witnessMessage hW).symm.trans
        (hproj.trans (D.projection_encode_eq_witnessMessage hW'))
  · intro hvalid α β hα hβ
    calc
      D.projection Y α = (D.extract Y α).message :=
        D.projection_eq_witnessMessage hα
      _ = (D.extract Y β).message :=
        hvalid (D.extract Y α) (D.extract Y β) (D.cnfSound hα) (D.cnfSound hβ)
      _ = D.projection Y β :=
        (D.projection_eq_witnessMessage hβ).symm

/-- Locked-core D.8 is sufficient for the valid-product-witness message
constancy appearing in the equivalence. -/
theorem validProductWitnessSingleMessage_of_lockedMessageRigidity
    (D : AppendixDProductBijectionCNFReadoutData
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux Var)
    (hrigid : D.product.core.LockedMessageRigidity)
    {Y : Public} (hY : D.product.support Y) :
    D.ValidProductWitnessSingleMessage Y := by
  intro W W' hW hW'
  exact D.product.singleMessagePromise_of_lockedMessageRigidity hrigid hY hW hW'

end AppendixDProductBijectionCNFReadoutData

/-- A product construction with exactly one non-public Boolean degree of
freedom: the quotient/message bit. -/
def bijectiveAmbiguousAppendixDProductConstruction :
    AppendixDProductConstruction Unit Bool Unit Bool Unit Unit Unit Unit where
  core := ambiguousAppendixDLockedCore
  support := fun _ => True
  publicLock := fun _ => ()
  gaugePredicate := fun _ _ _ => True
  bufferPredicate := fun _ _ _ => True
  auxPredicate := fun _ _ _ _ _ _ _ => True
  support_publicLock := by
    intro _ _
    trivial

/-- The canonical product witness carrying Boolean message `b`. -/
def bijectiveAmbiguousProductWitness (b : Bool) :
    bijectiveAmbiguousAppendixDProductConstruction.Witness where
  rawGauge := ()
  quotient := b
  lockAux := ()
  bufferAux := ()
  aux := ()
  message := b

/-- Every canonical Boolean product witness is valid. -/
theorem bijectiveAmbiguousProductWitness_valid (b : Bool) :
    bijectiveAmbiguousAppendixDProductConstruction.ValidWitness ()
      (bijectiveAmbiguousProductWitness b) := by
  simp [
    AppendixDProductConstruction.ValidWitness,
    bijectiveAmbiguousAppendixDProductConstruction,
    bijectiveAmbiguousProductWitness,
    ambiguousAppendixDLockedCore]

/-- The false and true canonical product witnesses have different messages. -/
theorem bijectiveAmbiguousProductWitness_false_message_ne_true :
    (bijectiveAmbiguousProductWitness false).message ≠
      (bijectiveAmbiguousProductWitness true).message := by
  intro h
  cases h

/-- Encode a canonical product witness by its Boolean message. -/
def encodeBijectiveAmbiguousProductWitness
    (W : bijectiveAmbiguousAppendixDProductConstruction.Witness) :
    ConcreteCNF.Assignment (Fin 1) :=
  fun _ => W.message

/-- Extract the canonical product witness from the one-variable CNF readout. -/
def extractBijectiveAmbiguousProductWitness
    (σ : ConcreteCNF.Assignment (Fin 1)) :
    bijectiveAmbiguousAppendixDProductConstruction.Witness :=
  bijectiveAmbiguousProductWitness (oneVarReadout σ)

/-- Encoding then extracting a valid witness returns the witness in the
canonical Boolean product countermodel. -/
theorem extract_encode_bijectiveAmbiguousProductWitness
    {W : bijectiveAmbiguousAppendixDProductConstruction.Witness}
    (hW : bijectiveAmbiguousAppendixDProductConstruction.ValidWitness () W) :
    extractBijectiveAmbiguousProductWitness
        (encodeBijectiveAmbiguousProductWitness W) = W := by
  cases W with
  | mk rawGauge quotient lockAux bufferAux aux message =>
      cases rawGauge
      cases lockAux
      cases bufferAux
      cases aux
      simp [
        extractBijectiveAmbiguousProductWitness,
        encodeBijectiveAmbiguousProductWitness,
        bijectiveAmbiguousProductWitness,
        oneVarReadout,
        AppendixDProductConstruction.ValidWitness,
        bijectiveAmbiguousAppendixDProductConstruction,
        ambiguousAppendixDLockedCore] at hW ⊢
      exact hW

/-- Extracting then encoding a satisfying assignment returns the assignment in
the one-variable CNF countermodel. -/
theorem encode_extract_bijectiveAmbiguousProductWitness
    {α : ConcreteCNF.Assignment (Fin 1)}
    (_hα : ConcreteCNF.IsSatFormula oneVarTautologyCNF α) :
    encodeBijectiveAmbiguousProductWitness
        (extractBijectiveAmbiguousProductWitness α) = α := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  rw [hi]
  rfl

/-- A bijective, exact CNF realization of the ambiguous product construction. -/
def bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData :
    AppendixDProductBijectionCNFReadoutData
      Unit Bool Unit Bool Unit Unit Unit Unit oneVarReadoutPublicVar where
  toAppendixDProductExactCNFReadoutData :=
    { product := bijectiveAmbiguousAppendixDProductConstruction
      formula := fun _ => oneVarTautologyCNF
      extract := fun _ σ => extractBijectiveAmbiguousProductWitness σ
      projection := fun _ σ => oneVarReadout σ
      cnfSound := by
        intro _ σ _
        exact bijectiveAmbiguousProductWitness_valid (oneVarReadout σ)
      projection_eq_witnessMessage := by
        intro _ _ _
        rfl
      satOnSupport := by
        intro _ _
        exact ⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩
      encode := fun _ W => encodeBijectiveAmbiguousProductWitness W
      encode_satisfies := by
        intro _ W _
        exact oneVarTautologyCNF_satisfied_any
          (encodeBijectiveAmbiguousProductWitness W)
      projection_encode_eq_witnessMessage := by
        intro _ W _
        rfl }
  extract_encode := by
    intro Y W hW
    cases Y
    exact extract_encode_bijectiveAmbiguousProductWitness hW
  encode_extract := by
    intro Y α hα
    cases Y
    exact encode_extract_bijectiveAmbiguousProductWitness hα

/-- The bijective exact CNF product countermodel does not have valid-witness
single-message constancy. -/
theorem bijectiveAmbiguousAppendixDProduct_not_validProductWitnessSingleMessage :
    ¬ AppendixDProductBijectionCNFReadoutData.ValidProductWitnessSingleMessage
        bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData () := by
  intro hsingle
  exact bijectiveAmbiguousProductWitness_false_message_ne_true
    (hsingle
      (bijectiveAmbiguousProductWitness false)
      (bijectiveAmbiguousProductWitness true)
      (bijectiveAmbiguousProductWitness_valid false)
      (bijectiveAmbiguousProductWitness_valid true))

/-- Therefore even bijective exact CNF realization does not force CNF
single-message readout. -/
theorem bijectiveAmbiguousAppendixDProduct_not_singleMessageReadout :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula
        (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.formula ()))
      (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.projection ()) := by
  intro hread
  exact bijectiveAmbiguousAppendixDProduct_not_validProductWitnessSingleMessage
    ((bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData
      |>.singleMessageReadout_iff_validProductWitnessSingleMessage ()).mp hread)

/-- The bijective exact CNF product countermodel has no message correct for all
arbitrary satisfying SAT-search outputs. -/
theorem bijectiveAmbiguousAppendixDProduct_not_exists_correctForAll :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula
          (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.formula ()))
        (bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.projection ())
        msg := by
  exact
    bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData
      |>.not_exists_correctForAllSatSearchOutputs_of_distinct_valid_witnessMessages
        (bijectiveAmbiguousProductWitness_valid false)
        (bijectiveAmbiguousProductWitness_valid true)
        bijectiveAmbiguousProductWitness_false_message_ne_true

/-- The bijective exact CNF product countermodel still refutes locked-core D.8. -/
theorem bijectiveAmbiguousAppendixDProduct_not_lockedMessageRigidity :
    ¬ AppendixDLockedCore.LockedMessageRigidity
        bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData.product.core := by
  exact
    bijectiveAmbiguousAppendixDProductBijectionCNFReadoutData
      |>.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
        (Y := ())
        trivial
        (bijectiveAmbiguousProductWitness_valid false)
        (bijectiveAmbiguousProductWitness_valid true)
        bijectiveAmbiguousProductWitness_false_message_ne_true

end Mettapedia.Computability.PNP
