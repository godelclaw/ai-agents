/-!
# PNP v13 crux ledger: upper-bound decoder readout constancy

This file is the first crux-first pass over `PNP-proof-v13.pdf`.
It deliberately avoids a broad Weakness/CD library and records only the theorem
surface needed to test one brittle central link.

## Ledger

1. `P=NP` upper-bound decoder.
   Endpoint claim: SAT decision gives SAT search, and SAT search plus the
   realization recovers the hidden message.  Crux: a SAT search procedure may
   return any satisfying witness, so the realization must prove that all
   satisfying witnesses have the same message readout.  The operational
   SAT-search interface below makes this exact: correctness for every valid
   SAT-search output is equivalent to a fixed-message readout theorem, and in
   the satisfiable case that is equivalent to single-message readout constancy.

2. CD evidence normalization.
   Crux statement still needed: every target-relevant non-neutral trace leaf is
   normalized into either a safe-buffer atom or a hidden-gauge atom, with no
   residual class that can carry message advantage.

3. Trace capture.
   Crux statement still needed: adaptive polynomial-time observers reduce to
   finite CD evidence traces without losing target-relevant advantage.

4. Atomic Evidence Budget.
   Crux statement still needed: safe-buffer leakage and hidden-gauge rank bound
   the coordinate-summed advantage without double-counting adaptive information.

5. Boundary-law mixing / product small-success.
   Crux statement still needed: every switched history used in the product
   theorem is admissible for the next pivot bit, so conditioning does not
   reintroduce predictive advantage.  The finite obstruction below shows that
   unconditional one-coordinate half-success bounds do not imply product decay.
   The repair target is a sequential conditional half-success theorem.  In the
   fixed-field instantiation layer, this becomes a per-cell balance theorem:
   every named history cell must contain at least as many next-failure points as
   next-success points.  Equivalently, each field cell needs an injection
   matching successful prefix points to unsuccessful prefix points in the same
   cell.  A field that already determines the next success bit can satisfy that
   balance only in the zero-success case.  This is not merely a head-step
   issue: the same blocker applies at any later fielded position after
   extending the history by the preceding success events.  In matching form,
   a valid recursive proof on a positive-mass next-success prefix proves the
   supplied field at that position does not determine the next success bit on
   the accumulated history support.  This prefix-relative form is stronger
   than the earlier global blocker: a field can be harmless globally but become
   success-revealing after conditioning on the current history.  The matching
   obligation is also pointwise: every successful prefix point must have an
   explicit same-cell failed prefix point, so one successful point whose
   accumulated-history cell contains only successes already blocks the route.
   Finally, any violation of the tower product inequality rules out the
   operational recursive matching proof itself, not just the wrapper
   certificate; the repeated Boolean-square one-cell fielded example exposes
   this directly at the fixed-field layer.  The product-bound contrapositive
   now localizes to an exact failed conditional prefix half-step in both the
   generic finite-switching interface and the v13 switched-coordinate list.
   The fixed-field localization theorem
   turns any failed recursive matching proof, and any product-bound failure,
   into a concrete failed fielded position `pre ++ item :: suffix`; in the
   repeated one-cell example, the exact failed position is the second cut after
   conditioning on the first success event.  At the fixed-field layer this now
   localizes further to a concrete supplied cell whose next-failure count is
   strictly smaller than its next-success count; in the repeated one-cell
   model that concrete cell has failure count `0` and success count `2`.
   The newest generic theorem removes the Boolean-square specialness: after a
   positive-mass event has occurred once, repeating the same event is never a
   valid second conditional half-step.  The v13 wrappers lift this to abstract,
   concrete-cell, fixed-field, and recursive matching interfaces.  The route
   synthesis layer keeps the conclusion precise: the fixed-field route is
   blocked under the explicit repeated-positive-pivot or bad-cell hypotheses;
   if the manuscript construction does not force those hypotheses, the repair
   target is the named recursive same-cell matching theorem, together with
   proofs that the repeated-pivot and bad-cell audit targets are absent.

6. Compression-from-success.
   Crux statement still needed: the product small-success bound yields the
   clocked `Kpoly` lower bound with all program-counting and clock dependencies
   explicit.

Chosen attacks for this cycle: item 1 and item 5.  The finite theorems below
isolate the exact readout-constancy obligation behind the constant-size decoder
under `P=NP`, then exhibit the smallest correlated-events obstruction to a
naive product small-success bound.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- A SAT-realization readout has the single-message property when every
satisfying witness projects to the same message. -/
def SingleMessageReadout {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) : Prop :=
  ∀ w₁ w₂, sat w₁ → sat w₂ → readout w₁ = readout w₂

/-- A stronger pointed form: every satisfying witness decodes to one fixed
message.  This is the shape needed by an arbitrary SAT-search upper-bound
decoder. -/
def FixedMessageReadout {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) (msg : Message) : Prop :=
  ∀ w, sat w → readout w = msg

/-- The output contract of a SAT-search subroutine on one satisfiable
realization: it may return any witness, but must return a satisfying one. -/
structure SatSearchOutput {Witness : Type u} (sat : Witness → Prop) where
  witness : Witness
  isSat : sat witness

/-- A decoder is correct for all valid SAT-search outputs when every satisfying
output witness decodes to the claimed message. -/
def CorrectForAllSatSearchOutputs {Witness : Type u} {Message : Type v}
    (sat : Witness → Prop) (readout : Witness → Message) (msg : Message) : Prop :=
  ∀ out : SatSearchOutput sat, readout out.witness = msg

/-- Correctness for one fixed message and arbitrary satisfying SAT-search output
implies readout constancy across all satisfying witnesses. -/
theorem singleMessageReadout_of_fixedMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : FixedMessageReadout sat readout msg) :
    SingleMessageReadout sat readout := by
  intro w₁ w₂ hw₁ hw₂
  exact (h w₁ hw₁).trans (h w₂ hw₂).symm

/-- Once one satisfying witness exists, readout constancy supplies a pointed
message to which every satisfying witness decodes. -/
theorem fixedMessageReadout_of_singleMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness}
    (hw₀ : sat w₀)
    (h : SingleMessageReadout sat readout) :
    FixedMessageReadout sat readout (readout w₀) := by
  intro w hw
  exact (h w w₀ hw hw₀)

/-- Correctness for all possible satisfying SAT-search outputs is exactly the
fixed-message readout obligation.  Thus a proof that uses SAT search cannot
hide behind a particular witness-selection policy. -/
theorem correctForAllSatSearchOutputs_iff_fixedMessageReadout
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message} :
    CorrectForAllSatSearchOutputs sat readout msg ↔
      FixedMessageReadout sat readout msg := by
  constructor
  · intro h w hw
    exact h ⟨w, hw⟩
  · intro h out
    exact h out.witness out.isSat

/-- Any claimed correctness theorem for all SAT-search outputs immediately
forces readout constancy across satisfying witnesses. -/
theorem singleMessageReadout_of_correctForAllSatSearchOutputs
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {msg : Message}
    (h : CorrectForAllSatSearchOutputs sat readout msg) :
    SingleMessageReadout sat readout := by
  exact singleMessageReadout_of_fixedMessageReadout
    (correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp h)

/-- In the satisfiable case, correctness for all SAT-search outputs at the
message read from one satisfying witness is equivalent to readout constancy. -/
theorem correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
    {Witness : Type u} {Message : Type v}
    {sat : Witness → Prop} {readout : Witness → Message}
    {w₀ : Witness} (hw₀ : sat w₀) :
    CorrectForAllSatSearchOutputs sat readout (readout w₀) ↔
      SingleMessageReadout sat readout := by
  constructor
  · intro h
    exact singleMessageReadout_of_correctForAllSatSearchOutputs h
  · intro h
    exact correctForAllSatSearchOutputs_iff_fixedMessageReadout.mpr
      (fixedMessageReadout_of_singleMessageReadout hw₀ h)

/-- The smallest finite obstruction: a satisfiable relation with two satisfying
witnesses and identity readout does not have the single-message property. -/
theorem not_singleMessageReadout_bool_true_id :
    ¬ SingleMessageReadout (fun _ : Bool => True) (fun w : Bool => w) := by
  intro h
  have hfalse : (fun _ : Bool => True) false := trivial
  have htrue : (fun _ : Bool => True) true := trivial
  have hread : false = true := h false true hfalse htrue
  cases hread

/-- Equivalently, the finite countermodel has two satisfying outputs with
distinct message readouts. -/
theorem exists_two_satisfying_outputs_with_distinct_readouts_bool_true_id :
    ∃ w₁ w₂ : Bool,
      (fun _ : Bool => True) w₁ ∧
      (fun _ : Bool => True) w₂ ∧
      (fun w : Bool => w) w₁ ≠ (fun w : Bool => w) w₂ := by
  exact ⟨false, true, trivial, trivial, by
    intro h
    cases h⟩

/-- The same two Boolean witnesses can be packaged as two valid SAT-search
outputs with different message readouts. -/
theorem exists_two_satSearchOutputs_with_distinct_readouts_bool_true_id :
    ∃ out₁ out₂ : SatSearchOutput (fun _ : Bool => True),
      (fun w : Bool => w) out₁.witness ≠ (fun w : Bool => w) out₂.witness := by
  exact ⟨⟨false, trivial⟩, ⟨true, trivial⟩, by
    intro h
    cases h⟩

/-- Therefore the fixed-message correctness condition is impossible for the
unconstrained two-witness Boolean realization.  This is the finite formal
obstruction to replacing the v13 single-message promise by bare SAT
satisfiability. -/
theorem not_exists_fixedMessageReadout_bool_true_id :
    ¬ ∃ msg : Bool,
      FixedMessageReadout (fun _ : Bool => True) (fun w : Bool => w) msg := by
  intro h
  cases h with
  | intro msg hmsg =>
      exact not_singleMessageReadout_bool_true_id
        (singleMessageReadout_of_fixedMessageReadout hmsg)

/-- Equivalently, no message is correct for all valid SAT-search outputs in the
unconstrained two-witness Boolean realization. -/
theorem not_exists_correctForAllSatSearchOutputs_bool_true_id :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (fun _ : Bool => True) (fun w : Bool => w) msg := by
  intro h
  rcases h with ⟨msg, hmsg⟩
  exact not_exists_fixedMessageReadout_bool_true_id
    ⟨msg, correctForAllSatSearchOutputs_iff_fixedMessageReadout.mp hmsg⟩

/-- Count the number of points of `Bool` satisfying an event.  This is a
two-point finite probability numerator, avoiding any probability-library
infrastructure for the product crux test. -/
def boolEventCount (E : Bool → Prop) [DecidablePred E] : Nat :=
  (if E false then 1 else 0) + (if E true then 1 else 0)

/-- Count the number of points of `Bool` satisfying two events simultaneously. -/
def boolJointEventCount (E F : Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Nat :=
  boolEventCount (fun ω => E ω ∧ F ω)

/-- The one-bit event used in the smallest product-success obstruction. -/
def boolSuccessEvent (ω : Bool) : Prop :=
  ω = true

/-- The one-bit success event is decidable by case analysis on the sample
point. -/
instance boolSuccessEvent_decidablePred : DecidablePred boolSuccessEvent := by
  intro ω
  cases ω <;> unfold boolSuccessEvent <;> infer_instance

/-- The event `ω = true` has uniform mass `1/2`, represented by numerator `1`
over the two-point sample space. -/
theorem boolSuccessEvent_count :
    boolEventCount boolSuccessEvent = 1 := by
  rfl

/-- Two identical copies of the same half-mass event still have joint mass
`1/2`, not `1/4`. -/
theorem boolSuccessEvent_joint_count :
    boolJointEventCount boolSuccessEvent boolSuccessEvent = 1 := by
  rfl

/-- Finite obstruction to a naive product-small-success step.  Both one-step
success events have numerator `1` over a two-point space, but the joint event
also has numerator `1`.  In denominator-free form, the false quarter-product
bound would require `4 * joint_count ≤ 2`. -/
theorem correlated_half_marginals_violate_quarter_product_bound :
    boolEventCount boolSuccessEvent = 1 ∧
      boolEventCount boolSuccessEvent = 1 ∧
      ¬ 4 * boolJointEventCount boolSuccessEvent boolSuccessEvent ≤ 2 := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- Count the number of points of `Bool × Bool` satisfying an event.  This is
the denominator-free numerator for the four-point uniform sample space. -/
def boolPairEventCount (E : Bool × Bool → Prop) [DecidablePred E] : Nat :=
  (if E (false, false) then 1 else 0) +
  (if E (false, true) then 1 else 0) +
  (if E (true, false) then 1 else 0) +
  (if E (true, true) then 1 else 0)

/-- Count simultaneous satisfaction on the four-point Boolean square. -/
def boolPairJointEventCount (E F : Bool × Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Nat :=
  boolPairEventCount (fun ω => E ω ∧ F ω)

/-- Denominator-free sequential half-success on `Bool × Bool`: the first event
has mass at most `1/2`, and the second has conditional mass at most `1/2`
inside the first event. -/
def SequentialHalfOnBoolPair (E F : Bool × Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Prop :=
  2 * boolPairEventCount E ≤ 4 ∧
    2 * boolPairJointEventCount E F ≤ boolPairEventCount E

/-- Sequential conditional half-success implies the two-step product bound.
This is the positive interface the v13 product-small-success step must supply,
in contrast to the unconditional marginal countermodel above. -/
theorem boolPair_product_bound_of_sequentialHalf
    (E F : Bool × Bool → Prop) [DecidablePred E] [DecidablePred F]
    (h : SequentialHalfOnBoolPair E F) :
    4 * boolPairJointEventCount E F ≤ 4 := by
  rcases h with ⟨hE, hF⟩
  have hmul := Nat.mul_le_mul_left 2 hF
  calc
    4 * boolPairJointEventCount E F =
        2 * (2 * boolPairJointEventCount E F) := by omega
    _ ≤ 2 * boolPairEventCount E := hmul
    _ ≤ 4 := hE

/-- First-coordinate success on the Boolean square. -/
def boolPairFirstSuccess (ω : Bool × Bool) : Prop :=
  ω.1 = true

/-- Second-coordinate success on the Boolean square. -/
def boolPairSecondSuccess (ω : Bool × Bool) : Prop :=
  ω.2 = true

instance boolPairFirstSuccess_decidablePred :
    DecidablePred boolPairFirstSuccess := by
  intro ω
  cases ω with
  | mk a b =>
      cases a <;> cases b <;> unfold boolPairFirstSuccess <;> infer_instance

instance boolPairSecondSuccess_decidablePred :
    DecidablePred boolPairSecondSuccess := by
  intro ω
  cases ω with
  | mk a b =>
      cases a <;> cases b <;> unfold boolPairSecondSuccess <;> infer_instance

/-- Each coordinate-success event has numerator `2` over the four-point square. -/
theorem boolPairFirstSuccess_count :
    boolPairEventCount boolPairFirstSuccess = 2 := by
  rfl

/-- Each coordinate-success event has numerator `2` over the four-point square. -/
theorem boolPairSecondSuccess_count :
    boolPairEventCount boolPairSecondSuccess = 2 := by
  rfl

/-- Independent coordinate-success events have numerator `1` intersection over
the four-point square. -/
theorem boolPairFirstSecondSuccess_joint_count :
    boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess = 1 := by
  rfl

/-- Coordinate-success events satisfy the sequential half-success interface. -/
theorem boolPairFirstSecondSuccess_sequentialHalf :
    SequentialHalfOnBoolPair boolPairFirstSuccess boolPairSecondSuccess := by
  constructor <;> decide

/-- The positive interface gives the expected denominator-free product bound on
the independent-coordinate finite model. -/
theorem boolPairFirstSecondSuccess_product_bound :
    4 * boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess ≤ 4 := by
  exact boolPair_product_bound_of_sequentialHalf _ _
    boolPairFirstSecondSuccess_sequentialHalf

/-- Reusing the same coordinate twice gives half-mass marginals but violates the
quarter-product bound on the four-point square. -/
theorem boolPair_correlated_half_marginals_violate_product_bound :
    boolPairEventCount boolPairFirstSuccess = 2 ∧
      boolPairEventCount boolPairFirstSuccess = 2 ∧
      ¬ 4 * boolPairJointEventCount boolPairFirstSuccess boolPairFirstSuccess ≤ 4 := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The correlated finite model fails exactly the second, conditional half-step:
inside the first event, the repeated event has conditional mass `1`, not
`1/2`. -/
theorem boolPair_correlated_marginals_fail_sequentialHalf :
    ¬ SequentialHalfOnBoolPair boolPairFirstSuccess boolPairFirstSuccess := by
  intro h
  exact
    (by
      decide :
        ¬ 2 * boolPairJointEventCount boolPairFirstSuccess boolPairFirstSuccess ≤
          boolPairEventCount boolPairFirstSuccess) h.2

end Mettapedia.Computability.PNP
