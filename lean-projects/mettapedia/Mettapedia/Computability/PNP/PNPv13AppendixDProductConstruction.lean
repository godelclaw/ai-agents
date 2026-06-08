import Mettapedia.Computability.PNP.PNPv13AppendixDPublicSyntaxDiscipline

/-!
# PNP v13: Appendix D product construction

This file formalizes the semantic core of Appendix D.36--D.41.  The product
construction combines a locked core with gauge, buffer, and auxiliary clauses.
Those extra layers do not create message rigidity: the D.41 single-message
promise follows from locked-message rigidity of the locked core, and a
counterexample to locked-message rigidity lifts through the product relation
when the extra layers are trivial.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y z q r s

/-- Appendix D.37 product witness shape, abstracting the raw gauge, quotient,
locked auxiliary, buffer auxiliary, local-gadget auxiliary, and message blocks. -/
structure AppendixDProductWitness
    (RawGauge : Type u) (Quotient : Type v) (LockAux : Type w)
    (BufferAux : Type x) (Aux : Type y) (Message : Type z) where
  rawGauge : RawGauge
  quotient : Quotient
  lockAux : LockAux
  bufferAux : BufferAux
  aux : Aux
  message : Message

/-- Appendix D.36--D.38 semantic product data.  `core` is the locked quotient
core; the remaining predicates are the gauge, buffer, and auxiliary clauses of
the product witness relation. -/
structure AppendixDProductConstruction
    (PublicLock : Type u) (Quotient : Type v) (LockAux : Type w)
    (Message : Type x) (Public : Type y) (RawGauge : Type z)
    (BufferAux : Type q) (Aux : Type r) where
  core : AppendixDLockedCore PublicLock Quotient LockAux Message
  support : Public → Prop
  publicLock : Public → PublicLock
  gaugePredicate : Public → RawGauge → Quotient → Prop
  bufferPredicate : Public → Quotient → BufferAux → Prop
  auxPredicate :
    Public → RawGauge → Quotient → LockAux → BufferAux → Aux → Message → Prop
  support_publicLock :
    ∀ {Y : Public}, support Y → core.support (publicLock Y)

namespace AppendixDProductConstruction

variable {PublicLock : Type u} {Quotient : Type v} {LockAux : Type w}
variable {Message : Type x} {Public : Type y} {RawGauge : Type z}
variable {BufferAux : Type q} {Aux : Type r}

abbrev Witness
    (_D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux) :=
  AppendixDProductWitness RawGauge Quotient LockAux BufferAux Aux Message

/-- Appendix D.38 product witness relation. -/
def ValidWitness
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    (Y : Public) (W : D.Witness) : Prop :=
  D.core.lockPredicate (D.publicLock Y) W.quotient W.lockAux W.message ∧
  D.core.readPredicate (D.publicLock Y) W.quotient W.lockAux W.message ∧
  D.gaugePredicate Y W.rawGauge W.quotient ∧
  D.bufferPredicate Y W.quotient W.bufferAux ∧
  D.auxPredicate Y W.rawGauge W.quotient W.lockAux W.bufferAux W.aux W.message

/-- The locked completion extracted from a product witness satisfying D.38. -/
def lockedCompletionOfValidWitness
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    {Y : Public} (W : D.Witness) (hW : D.ValidWitness Y W) :
    D.core.LockedCompletion (D.publicLock Y) where
  quotient := W.quotient
  lockAux := W.lockAux
  message := W.message
  lock_ok := hW.1
  read_ok := hW.2.1

/-- Appendix D.41: locked-message rigidity implies the product witness relation
has the single-message promise. -/
theorem singleMessagePromise_of_lockedMessageRigidity
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    (hrigid : D.core.LockedMessageRigidity) :
    ∀ {Y : Public} {W W' : D.Witness},
      D.support Y →
        D.ValidWitness Y W →
          D.ValidWitness Y W' →
            W.message = W'.message := by
  intro Y W W' hY hW hW'
  exact hrigid (D.support_publicLock hY)
    (D.lockedCompletionOfValidWitness W hW)
    (D.lockedCompletionOfValidWitness W' hW')

/-- Exact product-level obstruction: two valid product witnesses with different
messages refute locked-message rigidity of the underlying locked core. -/
theorem not_lockedMessageRigidity_of_distinct_valid_witnessMessages
    (D : AppendixDProductConstruction
      PublicLock Quotient LockAux Message Public RawGauge BufferAux Aux)
    {Y : Public} {W W' : D.Witness}
    (hY : D.support Y)
    (hW : D.ValidWitness Y W) (hW' : D.ValidWitness Y W')
    (hdiff : W.message ≠ W'.message) :
    ¬ D.core.LockedMessageRigidity := by
  intro hrigid
  exact hdiff (D.singleMessagePromise_of_lockedMessageRigidity hrigid hY hW hW')

end AppendixDProductConstruction

/-- A product construction using the neutral-public one-bit local locked core,
with trivial gauge, buffer, and auxiliary clauses. -/
def ambiguousAppendixDProductConstruction :
    AppendixDProductConstruction Unit (Unit → Bool) (Unit → Bool) (Unit → Bool)
      Unit Unit Unit Unit where
  core := ambiguousPublicSyntaxDisciplinedLocalCore.toAppendixDLockedCore
  support := fun _ => True
  publicLock := fun _ => ()
  gaugePredicate := fun _ _ _ => True
  bufferPredicate := fun _ _ _ => True
  auxPredicate := fun _ _ _ _ _ _ _ => True
  support_publicLock := by
    intro Y hY
    trivial

/-- The false product witness in the neutral-public countermodel. -/
def ambiguousAppendixDProductWitnessFalse :
    ambiguousAppendixDProductConstruction.Witness where
  rawGauge := ()
  quotient := singletonBoolBlock false
  lockAux := singletonBoolBlock false
  bufferAux := ()
  aux := ()
  message := singletonBoolBlock false

/-- The true product witness in the neutral-public countermodel. -/
def ambiguousAppendixDProductWitnessTrue :
    ambiguousAppendixDProductConstruction.Witness where
  rawGauge := ()
  quotient := singletonBoolBlock true
  lockAux := singletonBoolBlock false
  bufferAux := ()
  aux := ()
  message := singletonBoolBlock true

/-- The false product witness satisfies the D.38 product relation. -/
theorem ambiguousAppendixDProductWitnessFalse_valid :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      ambiguousAppendixDProductWitnessFalse := by
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
      ambiguousAppendixDProductWitnessFalse,
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble,
      singletonBoolBlock]

/-- The true product witness satisfies the D.38 product relation. -/
theorem ambiguousAppendixDProductWitnessTrue_valid :
    ambiguousAppendixDProductConstruction.ValidWitness ()
      ambiguousAppendixDProductWitnessTrue := by
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
      ambiguousAppendixDProductWitnessTrue,
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble,
      singletonBoolBlock]

/-- Gauge, buffer, and auxiliary product clauses do not repair the missing D.8
theorem: the neutral-public product construction has two valid witnesses with
different messages. -/
theorem ambiguousAppendixDProductConstruction_not_lockedMessageRigidity :
    ¬ ambiguousAppendixDProductConstruction.core.LockedMessageRigidity := by
  refine
    ambiguousAppendixDProductConstruction
      |>.not_lockedMessageRigidity_of_distinct_valid_witnessMessages
        (Y := ())
        (W := ambiguousAppendixDProductWitnessFalse)
        (W' := ambiguousAppendixDProductWitnessTrue)
        trivial
        ambiguousAppendixDProductWitnessFalse_valid
        ambiguousAppendixDProductWitnessTrue_valid ?_
  intro h
  have hpoint := congrFun h ()
  cases hpoint

end Mettapedia.Computability.PNP
