import Mathlib.Data.Fintype.Pi
import Mettapedia.Computability.PNP.PNPv13AppendixDLockedCore

/-!
# PNP v13: local Boolean Appendix D locked cores

Appendix D.5 says the locked and readout predicates are conjunctions of
bounded-arity local predicates.  This file makes that part explicit for Boolean
coordinate blocks and tests whether it can replace Appendix D.8.

It cannot: a one-bit local locked core with one public lock syntax, a trivial
locked predicate, and the arity-two deterministic readout predicate `M = z`
satisfies the local D.5/D.7 shape but has two locked completions with different
messages.
-/

namespace Mettapedia.Computability.PNP

universe u v w x

/-- Coordinates visible to a local Appendix D Boolean predicate. -/
inductive AppendixDLocalBoolCoord
    (QuotientCoord : Type u) (LockAuxCoord : Type v)
    (MessageCoord : Type w) where
  | quotient : QuotientCoord → AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord
  | lockAux : LockAuxCoord → AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord
  | message : MessageCoord → AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord

namespace AppendixDLocalBoolCoord

variable {QuotientCoord : Type u} {LockAuxCoord : Type v}
variable {MessageCoord : Type w}

/-- Combine quotient, locked-auxiliary, and message Boolean blocks into one
assignment on local predicate coordinates. -/
def assemble (z : QuotientCoord → Bool) (ξ : LockAuxCoord → Bool)
    (M : MessageCoord → Bool) :
    AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord → Bool
  | quotient q => z q
  | lockAux a => ξ a
  | message m => M m

end AppendixDLocalBoolCoord

/-- A local Boolean constraint: it sees only the coordinates in `scope`; its
acceptance predicate receives the restricted assignment on that finite scope. -/
structure BoolLocalConstraint (Coord : Type u) where
  scope : List Coord
  accept : (Fin scope.length → Bool) → Prop

namespace BoolLocalConstraint

variable {Coord : Type u}

/-- Evaluate a local constraint against a global Boolean assignment. -/
def eval (C : BoolLocalConstraint Coord) (σ : Coord → Bool) : Prop :=
  C.accept (fun i => σ (C.scope.get i))

end BoolLocalConstraint

/-- A finite conjunction of local constraints, each bounded by the same arity. -/
structure BoundedBoolLocalPredicate (Coord : Type u) where
  arityBound : Nat
  constraints : List (BoolLocalConstraint Coord)
  bounded :
    ∀ C ∈ constraints, C.scope.length ≤ arityBound

namespace BoundedBoolLocalPredicate

variable {Coord : Type u}

/-- Evaluate all local constraints in the bounded predicate. -/
def eval (P : BoundedBoolLocalPredicate Coord) (σ : Coord → Bool) : Prop :=
  ∀ C ∈ P.constraints, C.eval σ

/-- The empty conjunction, with an arbitrary arity bound. -/
def empty (Coord : Type u) (arityBound : Nat) :
    BoundedBoolLocalPredicate Coord where
  arityBound := arityBound
  constraints := []
  bounded := by
    intro C hC
    cases hC

end BoundedBoolLocalPredicate

/-- Appendix D locked-core data where `Lock` and `Read` are concretely given by
bounded local Boolean predicates over quotient, lock-auxiliary, and message
coordinate blocks. -/
structure AppendixDLocalBoolLockedCore
    (PublicLock : Type u) (QuotientCoord : Type v)
    (LockAuxCoord : Type w) (MessageCoord : Type x) where
  publicLockFinite : Fintype PublicLock
  quotientCoordDecidableEq : DecidableEq QuotientCoord
  quotientCoordFinite : Fintype QuotientCoord
  lockAuxCoordDecidableEq : DecidableEq LockAuxCoord
  lockAuxCoordFinite : Fintype LockAuxCoord
  messageCoordDecidableEq : DecidableEq MessageCoord
  messageCoordFinite : Fintype MessageCoord
  support : PublicLock → Prop
  lockLocal :
    PublicLock →
      BoundedBoolLocalPredicate
        (AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord)
  readLocal :
    PublicLock →
      BoundedBoolLocalPredicate
        (AppendixDLocalBoolCoord QuotientCoord LockAuxCoord MessageCoord)

namespace AppendixDLocalBoolLockedCore

variable {PublicLock : Type u} {QuotientCoord : Type v}
variable {LockAuxCoord : Type w} {MessageCoord : Type x}

/-- Forget the local presentation to the Appendix D.5 locked core interface. -/
def toAppendixDLockedCore
    (C : AppendixDLocalBoolLockedCore
      PublicLock QuotientCoord LockAuxCoord MessageCoord) :
    AppendixDLockedCore
      PublicLock (QuotientCoord → Bool) (LockAuxCoord → Bool)
      (MessageCoord → Bool) where
  publicLockFinite := C.publicLockFinite
  quotientFinite := by
    letI : DecidableEq QuotientCoord := C.quotientCoordDecidableEq
    letI : Fintype QuotientCoord := C.quotientCoordFinite
    exact inferInstance
  lockAuxFinite := by
    letI : DecidableEq LockAuxCoord := C.lockAuxCoordDecidableEq
    letI : Fintype LockAuxCoord := C.lockAuxCoordFinite
    exact inferInstance
  messageFinite := by
    letI : DecidableEq MessageCoord := C.messageCoordDecidableEq
    letI : Fintype MessageCoord := C.messageCoordFinite
    exact inferInstance
  support := C.support
  lockPredicate := fun Y z ξ M =>
    (C.lockLocal Y).eval (AppendixDLocalBoolCoord.assemble z ξ M)
  readPredicate := fun Y z ξ M =>
    (C.readLocal Y).eval (AppendixDLocalBoolCoord.assemble z ξ M)

end AppendixDLocalBoolLockedCore

/-- The arity-two readout constraint `M = z` for the one-bit local core. -/
def oneBitReadEqualsQuotientConstraint :
    BoolLocalConstraint (AppendixDLocalBoolCoord Unit Unit Unit) where
  scope := [
    AppendixDLocalBoolCoord.quotient (),
    AppendixDLocalBoolCoord.message ()]
  accept := fun values => values 0 = values 1

/-- The one-bit read predicate is the single local constraint `M = z`. -/
def oneBitReadEqualsQuotientPredicate :
    BoundedBoolLocalPredicate (AppendixDLocalBoolCoord Unit Unit Unit) where
  arityBound := 2
  constraints := [oneBitReadEqualsQuotientConstraint]
  bounded := by
    intro C hC
    simp [oneBitReadEqualsQuotientConstraint] at hC
    subst C
    simp

/-- Boolean assignment on a singleton coordinate block. -/
def singletonBoolBlock (b : Bool) : Unit → Bool :=
  fun _ => b

/-- A local D.5-style locked core with no public message tag.  The public syntax
is a singleton, `Lock` has no clauses, and `Read` is the local arity-two
predicate `M = z`. -/
def ambiguousAppendixDLocalBoolLockedCore :
    AppendixDLocalBoolLockedCore Unit Unit Unit Unit where
  publicLockFinite := inferInstance
  quotientCoordDecidableEq := inferInstance
  quotientCoordFinite := inferInstance
  lockAuxCoordDecidableEq := inferInstance
  lockAuxCoordFinite := inferInstance
  messageCoordDecidableEq := inferInstance
  messageCoordFinite := inferInstance
  support := fun _ => True
  lockLocal := fun _ =>
    BoundedBoolLocalPredicate.empty
      (AppendixDLocalBoolCoord Unit Unit Unit) 0
  readLocal := fun _ => oneBitReadEqualsQuotientPredicate

/-- The false completion of the local one-bit core. -/
def ambiguousAppendixDLocalCompletionFalse :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore
      |>.LockedCompletion () where
  quotient := singletonBoolBlock false
  lockAux := singletonBoolBlock false
  message := singletonBoolBlock false
  lock_ok := by
    intro C hC
    cases hC
  read_ok := by
    intro C hC
    simp [
      ambiguousAppendixDLocalBoolLockedCore,
      oneBitReadEqualsQuotientPredicate] at hC
    subst C
    simp [
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble,
      singletonBoolBlock]

/-- The true completion of the local one-bit core. -/
def ambiguousAppendixDLocalCompletionTrue :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore
      |>.LockedCompletion () where
  quotient := singletonBoolBlock true
  lockAux := singletonBoolBlock false
  message := singletonBoolBlock true
  lock_ok := by
    intro C hC
    cases hC
  read_ok := by
    intro C hC
    simp [
      ambiguousAppendixDLocalBoolLockedCore,
      oneBitReadEqualsQuotientPredicate] at hC
    subst C
    simp [
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble,
      singletonBoolBlock]

/-- The local one-bit core satisfies Appendix D.7. -/
theorem ambiguousAppendixDLocalBoolLockedCore_lockSatisfiable :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore.LockSatisfiable := by
  intro Y _
  cases Y
  exact ⟨ambiguousAppendixDLocalCompletionFalse⟩

/-- The local one-bit core has deterministic readout for each fixed readout
state `(Y,z,ξ_lock)`. -/
theorem ambiguousAppendixDLocalBoolLockedCore_readDeterministic :
    ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore.ReadDeterministic := by
  intro Y z ξ M M' hM hM'
  cases Y
  have hM_eval := hM oneBitReadEqualsQuotientConstraint (by simp [
    ambiguousAppendixDLocalBoolLockedCore,
    oneBitReadEqualsQuotientPredicate])
  have hM'_eval := hM' oneBitReadEqualsQuotientConstraint (by simp [
    ambiguousAppendixDLocalBoolLockedCore,
    oneBitReadEqualsQuotientPredicate])
  have hM_eq : z () = M () := by
    simpa [
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble] using hM_eval
  have hM'_eq : z () = M' () := by
    simpa [
      BoolLocalConstraint.eval,
      oneBitReadEqualsQuotientConstraint,
      AppendixDLocalBoolCoord.assemble] using hM'_eval
  funext m
  cases m
  exact hM_eq.symm.trans hM'_eq

/-- The local D.5/D.7/deterministic-readout shape still does not imply D.8:
the false and true completions have different messages. -/
theorem ambiguousAppendixDLocalBoolLockedCore_not_lockedMessageRigidity :
    ¬ AppendixDLockedCore.LockedMessageRigidity
        ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore := by
  refine
    AppendixDLockedCore.not_lockedMessageRigidity_of_distinct_completions
      ambiguousAppendixDLocalBoolLockedCore.toAppendixDLockedCore
      (Y := ())
      trivial
      ambiguousAppendixDLocalCompletionFalse
      ambiguousAppendixDLocalCompletionTrue ?_
  intro h
  have hpoint := congrFun h ()
  cases hpoint

end Mettapedia.Computability.PNP
