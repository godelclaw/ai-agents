import Mathlib.Data.Fintype.Card

/-!
# Finite switching admissibility

This file isolates the generic finite product argument needed by the PNP v13
boundary-law/product-success route.  It does not assert that the manuscript's
switched histories satisfy the hypotheses.  Instead it records the exact
counting interface a successful switching theorem must instantiate.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- A finite event packaged with its decidability data. -/
structure FiniteEvent (Ω : Type u) where
  pred : Ω → Prop
  decidablePred : DecidablePred pred

attribute [instance] FiniteEvent.decidablePred

/-- Counting numerator for a decidable event on a finite sample space. -/
def finiteEventCount (Ω : Type u) [Fintype Ω]
    (E : Ω → Prop) [DecidablePred E] : Nat :=
  Fintype.card {ω : Ω // E ω}

/-- Monotonicity of finite event counts under pointwise implication. -/
theorem finiteEventCount_le_of_imp {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) :
    finiteEventCount Ω E ≤ finiteEventCount Ω F := by
  let emb : {ω : Ω // E ω} → {ω : Ω // F ω} :=
    fun ω => ⟨ω.1, h ω.1 ω.2⟩
  exact Fintype.card_le_of_injective emb (by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : {ω : Ω // F ω} => x.1) hab))

/-- The event that all events in a finite history hold. -/
def allEvents {Ω : Type u} : List (FiniteEvent Ω) → Ω → Prop
  | [], _ => True
  | E :: Es, ω => E.pred ω ∧ allEvents Es ω

instance allEvents_decidablePred {Ω : Type u} :
    (events : List (FiniteEvent Ω)) → DecidablePred (allEvents events)
  | [] => fun _ => isTrue trivial
  | E :: Es => fun ω => by
      haveI : DecidablePred (allEvents Es) := allEvents_decidablePred Es
      exact inferInstanceAs (Decidable (E.pred ω ∧ allEvents Es ω))

/-- Count the sample points satisfying every event in a finite history. -/
def finiteHistoryCount (Ω : Type u) [Fintype Ω]
    (events : List (FiniteEvent Ω)) : Nat :=
  finiteEventCount Ω (allEvents events)

/-- If a point satisfies an extended history, then it satisfies the prefix. -/
theorem allEvents_of_append {Ω : Type u}
    (hist tail : List (FiniteEvent Ω)) {ω : Ω}
    (h : allEvents (hist ++ tail) ω) :
    allEvents hist ω := by
  induction hist with
  | nil =>
      trivial
  | cons E hist ih =>
      exact ⟨h.1, ih h.2⟩

/-- Adding more events to a finite history can only shrink its count. -/
theorem finiteHistoryCount_append_le {Ω : Type u} [Fintype Ω]
    (hist tail : List (FiniteEvent Ω)) :
    finiteHistoryCount Ω (hist ++ tail) ≤ finiteHistoryCount Ω hist := by
  exact finiteEventCount_le_of_imp (fun ω h => allEvents_of_append hist tail h)

/-- A one-step half-success/admissibility condition relative to an existing
finite history. -/
def PrefixHalfStep {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω) : Prop :=
  2 * finiteHistoryCount Ω (hist ++ [E]) ≤ finiteHistoryCount Ω hist

/-- Empty current histories are automatically admissible for the next step. -/
theorem prefixHalfStep_of_historyCount_eq_zero {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} (E : FiniteEvent Ω)
    (hzero : finiteHistoryCount Ω hist = 0) :
    PrefixHalfStep hist E := by
  have hle := finiteHistoryCount_append_le (Ω := Ω) hist [E]
  have hz : finiteHistoryCount Ω (hist ++ [E]) = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hzero] using hle)
  simp [PrefixHalfStep, hzero, hz]

/-- Sequential half-admissibility from an existing history: each next event cuts
the current history class by at most a factor of two, in finite counting form. -/
def SequentialHalfAdmissibleFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (FiniteEvent Ω) → Prop
  | [] => True
  | E :: rest =>
      2 * finiteHistoryCount Ω (hist ++ [E]) ≤ finiteHistoryCount Ω hist ∧
        SequentialHalfAdmissibleFrom (hist ++ [E]) rest

/-- Sequential half-admissibility from the empty public history. -/
def SequentialHalfAdmissible {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω)) : Prop :=
  SequentialHalfAdmissibleFrom ([] : List (FiniteEvent Ω)) events

/-- The first obligation in a nonempty sequential-admissibility proof is the
corresponding prefix half-step. -/
theorem prefixHalfStep_of_sequentialHalfAdmissibleFrom_cons
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    (h : SequentialHalfAdmissibleFrom hist (E :: rest)) :
    PrefixHalfStep hist E := by
  exact h.1

/-- A failed one-step conditional half-success obligation blocks the whole
remaining switching history. -/
theorem not_sequentialHalfAdmissibleFrom_cons_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    (hfail : ¬ PrefixHalfStep hist E) :
    ¬ SequentialHalfAdmissibleFrom hist (E :: rest) := by
  intro h
  exact hfail (prefixHalfStep_of_sequentialHalfAdmissibleFrom_cons h)

/-- In a two-step history, failure of the second conditional half-step blocks
sequential admissibility, even if both events have good unconditional
marginals. -/
theorem not_sequentialHalfAdmissible_pair_of_not_second_prefixHalfStep
    {Ω : Type u} [Fintype Ω] {E F : FiniteEvent Ω}
    (hfail : ¬ PrefixHalfStep [E] F) :
    ¬ SequentialHalfAdmissible [E, F] := by
  intro h
  exact hfail (prefixHalfStep_of_sequentialHalfAdmissibleFrom_cons h.2)

lemma finiteHistoryCount_append_cons {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω)
    (rest : List (FiniteEvent Ω)) :
    finiteHistoryCount Ω (hist ++ E :: rest) =
      finiteHistoryCount Ω ((hist ++ [E]) ++ rest) := by
  rw [List.append_assoc]
  rfl

/-- Generic finite tower-product bound for sequential half-admissible event
histories.  This is the finite switching/admissibility theorem behind the v13
product-success repair obligation. -/
theorem finiteHistory_product_bound_of_sequentialHalfFrom
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissibleFrom hist rest) :
    2 ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
      finiteHistoryCount Ω hist := by
  induction rest generalizing hist with
  | nil =>
      simp [finiteHistoryCount]
  | cons E rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have ih' := ih (hist ++ [E]) hrest
      have hmul := Nat.mul_le_mul_left 2 ih'
      calc
        2 ^ (E :: rest).length * finiteHistoryCount Ω (hist ++ E :: rest)
            = 2 * (2 ^ rest.length *
                finiteHistoryCount Ω ((hist ++ [E]) ++ rest)) := by
                rw [finiteHistoryCount_append_cons]
                simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
        _ ≤ 2 * finiteHistoryCount Ω (hist ++ [E]) := hmul
        _ ≤ finiteHistoryCount Ω hist := hstep

/-- Product bound from the empty history. -/
theorem finiteHistory_product_bound_of_sequentialHalf
    {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissible events) :
    2 ^ events.length * finiteHistoryCount Ω events ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact finiteHistory_product_bound_of_sequentialHalfFrom
    ([] : List (FiniteEvent Ω)) events h

/-- Contrapositive form of the tower-product theorem: if the final
intersection is too large for the claimed sequence of half-steps, then the
sequence cannot be sequentially half-admissible. -/
theorem not_sequentialHalfAdmissibleFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)}
    (hbad :
      ¬ 2 ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
        finiteHistoryCount Ω hist) :
    ¬ SequentialHalfAdmissibleFrom hist rest := by
  intro h
  exact hbad (finiteHistory_product_bound_of_sequentialHalfFrom hist rest h)

/-- Empty-history contrapositive of the tower-product theorem. -/
theorem not_sequentialHalfAdmissible_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {events : List (FiniteEvent Ω)}
    (hbad :
      ¬ 2 ^ events.length * finiteHistoryCount Ω events ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ SequentialHalfAdmissible events := by
  intro h
  exact hbad (finiteHistory_product_bound_of_sequentialHalf events h)

end Mettapedia.Computability.PNP
