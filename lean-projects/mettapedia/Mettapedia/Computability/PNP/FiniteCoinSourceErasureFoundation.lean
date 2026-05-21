import Mettapedia.Computability.PNP.FiniteCountIndependenceFoundation

/-!
# P vs NP grassroots: finite-coin source erasure

The balanced-fiber obstruction says that a finite-coin recoding can decorrelate
its marginal output only by erasing source evidence from output fibers.  This
file turns that idea into reusable definitions:

* predicate neutrality: every decidable output property has the same count on
  true-side and false-side coin samples;
* decoder half-accuracy: every Boolean output decoder has exactly random-guess
  aggregate accuracy across the two source sides;
* the equivalence between balanced output fibers and predicate-level erasure.

These statements are grassroots infrastructure.  The crux modules remain the
place where source-preserving side channels are shown to force large
finite-count defects.
-/

namespace Mettapedia.Computability.PNP

/-- A decidable output predicate is source-neutral for a finite-coin recoding
when it selects the same number of true-side and false-side coin values. -/
def finiteCoinOutputPredicateNeutral {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] : Prop :=
  finiteEventCount Coin (fun c => P (r true c)) =
    finiteEventCount Coin (fun c => P (r false c))

/-- A finite-coin output is predicate-erasing when every decidable output
property is source-neutral. -/
def FiniteCoinOutputPredicateErasing {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) : Prop :=
  ∀ P : α → Prop, [DecidablePred P] → finiteCoinOutputPredicateNeutral r P

/-- The two source sides have separated output ranges when no true-side output
can also occur as a false-side output. -/
def FiniteCoinSourceRangesSeparated {Coin α : Type*}
    (r : Bool → Coin → α) : Prop :=
  ∀ cTrue cFalse : Coin, r true cTrue ≠ r false cFalse

/-- Predicate erasure is exactly balanced output fibers when the output type has
decidable equality.  This is the grassroots form of the balanced-fiber fork:
fiber balance is not just a cancellation trick; it is precisely neutrality for
all decidable output predicates. -/
theorem finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro hbal P _hP
    exact finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal
  · intro herase y
    have hneutral := herase (fun z : α => z = y)
    simpa [finiteCoinOutputPredicateNeutral, coinTrueFiberCount, coinFalseFiberCount]
      using hneutral

/-- Balanced finite-coin fibers erase every decidable output predicate. -/
theorem finiteCoinOutputPredicateErasing_of_fiberBalanced
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinOutputPredicateErasing r :=
  (finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing r).mp hbal

/-- Predicate erasure implies balanced finite-coin fibers. -/
theorem finiteCoinRecodingFiberBalanced_of_outputPredicateErasing
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinRecodingFiberBalanced r :=
  (finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing r).mpr herase

/-- A strict true-side count advantage for one output predicate refutes
predicate erasure. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputPredicate_trueCount_gt_falseCount
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  intro herase
  exact (Nat.ne_of_gt hgt) (herase P)

/-- A strict false-side count advantage for one output predicate refutes
predicate erasure. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputPredicate_falseCount_gt_trueCount
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  intro herase
  exact (Nat.ne_of_gt hgt) (herase P).symm

/-- Uniform predicate separation is incompatible with predicate erasure on a
nonempty coin space. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputPredicate_separates
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  intro herase
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  have htruePos : 0 < finiteEventCount Coin (fun c => P (r true c)) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨c₀, htrue c₀⟩⟩
  have hfalseZero :
      finiteEventCount Coin (fun c => P (r false c)) = 0 := by
    exact finiteEventCount_zero_of_forall_not
      (fun c => P (r false c)) (fun c hc => hfalse c hc)
  have htrueZero :
      finiteEventCount Coin (fun c => P (r true c)) = 0 := by
    exact (herase P).trans hfalseZero
  exact (Nat.ne_of_gt htruePos) htrueZero

/-- Disjoint true-side and false-side output ranges are incompatible with
predicate erasure on a nonempty coin space. -/
theorem not_finiteCoinOutputPredicateErasing_of_sourceRangesSeparated
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hsep : FiniteCoinSourceRangesSeparated r) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputPredicate_separates
    r (fun y => ∃ c : Coin, r true c = y)
    (fun c => ⟨c, rfl⟩)
    (fun cFalse h => by
      rcases h with ⟨cTrue, hEq⟩
      exact hsep cTrue cFalse hEq)

/-- Aggregate correct count of a Boolean decoder across true-side and
false-side coin samples. -/
def finiteCoinOutputDecoderCorrectCount {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool) : Nat :=
  finiteEventCount Coin (fun c => decode (r true c) = true) +
    finiteEventCount Coin (fun c => decode (r false c) = false)

/-- A Boolean output decoder is exactly half-accurate, in division-free form,
when its aggregate correct count across the two source sides is `|Coin|`. -/
def finiteCoinOutputDecoderHalfAccurate {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool) : Prop :=
  finiteCoinOutputDecoderCorrectCount r decode = Fintype.card Coin

/-- A finite-coin output is source-recovering when some Boolean decoder
uniformly recovers the source bit from the output. -/
def FiniteCoinOutputSourceRecovering {Coin α : Type*}
    (r : Bool → Coin → α) : Prop :=
  ∃ decode : α → Bool,
    (∀ c : Coin, decode (r true c) = true) ∧
      ∀ c : Coin, decode (r false c) = false

/-- Predicate erasure forces every Boolean output decoder to be exactly
half-accurate in aggregate. -/
theorem finiteCoinOutputDecoderHalfAccurate_of_outputPredicateErasing
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (herase : FiniteCoinOutputPredicateErasing r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  have hpred := herase (fun y => decode y = true)
  unfold finiteCoinOutputDecoderHalfAccurate finiteCoinOutputDecoderCorrectCount
  rw [hpred]
  exact finiteEventCount_bool_true_add_false (fun c => decode (r false c))

/-- Balanced finite-coin fibers force every Boolean output decoder to be exactly
half-accurate in aggregate. -/
theorem finiteCoinOutputDecoderHalfAccurate_of_fiberBalanced
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  exact finiteCoinOutputDecoderHalfAccurate_of_outputPredicateErasing r decode
    (finiteCoinOutputPredicateErasing_of_fiberBalanced r hbal)

/-- Better-than-half aggregate decoder accuracy refutes predicate erasure. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputDecoder_correctCount_gt_card
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin < finiteCoinOutputDecoderCorrectCount r decode) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  intro herase
  exact (Nat.ne_of_gt hgt)
    (finiteCoinOutputDecoderHalfAccurate_of_outputPredicateErasing r decode herase)

/-- A Boolean decoder that uniformly recovers the source bit is incompatible
with predicate erasure on a nonempty coin space. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputDecoder_recovers
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  exact not_finiteCoinOutputPredicateErasing_of_outputPredicate_separates
    r (fun y => decode y = true) htrue (fun c h => by
      have hdecodeFalse : decode (r false c) = false := hfalse c
      rw [h] at hdecodeFalse
      cases hdecodeFalse)

/-- Separated source ranges yield an explicit source-recovering Boolean decoder
by testing membership in the true-side output range. -/
theorem finiteCoinOutputSourceRecovering_of_sourceRangesSeparated
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α)
    (hsep : FiniteCoinSourceRangesSeparated r) :
    FiniteCoinOutputSourceRecovering r := by
  refine ⟨fun y => if ∃ c : Coin, r true c = y then true else false, ?_, ?_⟩
  · intro c
    simp
  · intro cFalse
    have hnot : ¬ ∃ cTrue : Coin, r true cTrue = r false cFalse := by
      intro h
      rcases h with ⟨cTrue, hEq⟩
      exact hsep cTrue cFalse hEq
    simp [hnot]

/-- Source-recovering finite-coin outputs are incompatible with predicate
erasure on a nonempty coin space. -/
theorem not_finiteCoinOutputPredicateErasing_of_outputSourceRecovering
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin]
    (r : Bool → Coin → α)
    (hrec : FiniteCoinOutputSourceRecovering r) :
    ¬ FiniteCoinOutputPredicateErasing r := by
  rcases hrec with ⟨decode, htrue, hfalse⟩
  exact not_finiteCoinOutputPredicateErasing_of_outputDecoder_recovers
    r decode htrue hfalse

end Mettapedia.Computability.PNP
