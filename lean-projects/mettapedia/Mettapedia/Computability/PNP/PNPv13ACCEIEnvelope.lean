import Mettapedia.Computability.PNP.FiniteSwitchingAdmissibility
import Mathlib.Tactic

/-!
# PNP v13 ACCEI envelope and sequential product skeleton

Section 9 of the v13 manuscript converts an averaged ACCEI envelope into a
large pruned set of switched coordinates, then applies a tower-product bound on
the pruned sequence.  This file isolates the finite counting skeleton of that
move.  It does not claim that the manuscript's analytic ACCEI hypotheses hold;
it records the exact finite obligations they must instantiate.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u v

/-- Coordinates whose ACCEI envelope value is at most a chosen threshold. -/
def acceiGoodCount (ι : Type u) [Fintype ι]
    (η : ι → ℕ) (threshold : ℕ) : ℕ :=
  (Finset.univ.filter fun i : ι => η i ≤ threshold).card

/-- Coordinates whose ACCEI envelope value exceeds a chosen threshold. -/
def acceiBadCount (ι : Type u) [Fintype ι]
    (η : ι → ℕ) (threshold : ℕ) : ℕ :=
  (Finset.univ.filter fun i : ι => threshold < η i).card

/-- Good and bad ACCEI indices partition the finite switched-coordinate set. -/
theorem acceiGoodCount_add_acceiBadCount
    (ι : Type u) [Fintype ι] (η : ι → ℕ) (threshold : ℕ) :
    acceiGoodCount ι η threshold + acceiBadCount ι η threshold =
      Fintype.card ι := by
  classical
  unfold acceiGoodCount acceiBadCount
  let good : Finset ι := Finset.univ.filter fun i : ι => η i ≤ threshold
  let bad : Finset ι := Finset.univ.filter fun i : ι => threshold < η i
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro i hgood hbad
    exact not_lt_of_ge (Finset.mem_filter.mp hgood).2 (Finset.mem_filter.mp hbad).2
  have hunion : good ∪ bad = Finset.univ := by
    ext i
    by_cases hgood : η i ≤ threshold
    · simp [good, bad, hgood]
    · have hbad : threshold < η i := by omega
      simp [good, bad, hgood, hbad]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ] at hcard
  exact hcard.symm

/-- Bad ACCEI coordinates are exactly the complement count of the pruned good
coordinates. -/
theorem acceiBadCount_eq_card_sub_acceiGoodCount
    (ι : Type u) [Fintype ι] (η : ι → ℕ) (threshold : ℕ) :
    acceiBadCount ι η threshold =
      Fintype.card ι - acceiGoodCount ι η threshold := by
  have hpartition := acceiGoodCount_add_acceiBadCount ι η threshold
  omega

/-- Finite Markov-pruning count: every bad coordinate contributes at least
`threshold + 1` to the total envelope. -/
theorem acceiBadCount_mul_succ_threshold_le_sum
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold : ℕ) :
    acceiBadCount ι η threshold * (threshold + 1) ≤ ∑ i, η i := by
  classical
  unfold acceiBadCount
  let bad : Finset ι := Finset.univ.filter fun i : ι => threshold < η i
  calc
    bad.card * (threshold + 1) = bad.sum (fun _ => threshold + 1) := by
      simp [Nat.mul_comm]
    _ ≤ bad.sum η := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2
    _ ≤ Finset.univ.sum η := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun i : ι => threshold < η i) Finset.univ)
        (by intro _ _ _; exact Nat.zero_le _)

/-- Budgeted Markov-pruning count: if the total ACCEI envelope is at most
`budget`, then the bad-coordinate count is budgeted by `threshold + 1`. -/
theorem acceiBadCount_mul_succ_threshold_le_of_sum_le
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    acceiBadCount ι η threshold * (threshold + 1) ≤ budget :=
  le_trans (acceiBadCount_mul_succ_threshold_le_sum η threshold) hbudget

/-- Budgeted Markov pruning, written as a complement-count bound. -/
theorem card_sub_acceiGoodCount_mul_succ_threshold_le_of_sum_le
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    (Fintype.card ι - acceiGoodCount ι η threshold) *
        (threshold + 1) ≤ budget := by
  simpa [acceiBadCount_eq_card_sub_acceiGoodCount ι η threshold] using
    acceiBadCount_mul_succ_threshold_le_of_sum_le
      η threshold budget hbudget

/-- Division-form Markov pruning: at most `budget / (threshold + 1)`
coordinates can exceed the ACCEI threshold. -/
theorem acceiBadCount_le_budget_div_succ_threshold_of_sum_le
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    acceiBadCount ι η threshold ≤ budget / (threshold + 1) := by
  exact
    (Nat.le_div_iff_mul_le (Nat.succ_pos threshold)).mpr
      (acceiBadCount_mul_succ_threshold_le_of_sum_le
        η threshold budget hbudget)

/-- The pruned good coordinates are large up to the finite Markov loss
`budget / (threshold + 1)`. -/
theorem card_le_acceiGoodCount_add_budget_div_succ_threshold_of_sum_le
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    Fintype.card ι ≤
      acceiGoodCount ι η threshold + budget / (threshold + 1) := by
  have hpartition := acceiGoodCount_add_acceiBadCount ι η threshold
  have hbad :
      acceiBadCount ι η threshold ≤ budget / (threshold + 1) :=
    acceiBadCount_le_budget_div_succ_threshold_of_sum_le
      η threshold budget hbudget
  calc
    Fintype.card ι =
        acceiGoodCount ι η threshold + acceiBadCount ι η threshold := by
      exact hpartition.symm
    _ ≤ acceiGoodCount ι η threshold + budget / (threshold + 1) := by
      exact Nat.add_le_add_left hbad _

/-- Equivalently, the good-coordinate count is at least total coordinates
minus the finite Markov loss. -/
theorem card_sub_budget_div_succ_threshold_le_acceiGoodCount_of_sum_le
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    Fintype.card ι - budget / (threshold + 1) ≤
      acceiGoodCount ι η threshold := by
  have hlarge :=
    card_le_acceiGoodCount_add_budget_div_succ_threshold_of_sum_le
      η threshold budget hbudget
  omega

/-- If the finite Markov loss is smaller than the coordinate set, at least one
coordinate survives the ACCEI pruning threshold. -/
theorem exists_accei_good_of_budget_div_succ_threshold_lt_card
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget)
    (hloss : budget / (threshold + 1) < Fintype.card ι) :
    ∃ i : ι, η i ≤ threshold := by
  classical
  have hgood_lower :=
    card_sub_budget_div_succ_threshold_le_acceiGoodCount_of_sum_le
      η threshold budget hbudget
  have hpositive : 0 < acceiGoodCount ι η threshold := by
    omega
  unfold acceiGoodCount at hpositive
  rcases Finset.card_pos.mp hpositive with ⟨i, hi⟩
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- A two-coordinate envelope that makes the finite Markov ACCEI loss exact:
`false` is good and `true` is one unit above the threshold. -/
def oneGoodOneBadACCEIEnvelope (threshold : ℕ) : Bool → ℕ
  | false => 0
  | true => threshold + 1

/-- The sharp two-coordinate envelope has total ACCEI budget exactly
`threshold + 1`. -/
theorem oneGoodOneBadACCEIEnvelope_sum (threshold : ℕ) :
    (∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b) =
      threshold + 1 := by
  simp [oneGoodOneBadACCEIEnvelope]

/-- The sharp two-coordinate envelope has exactly one good coordinate. -/
theorem oneGoodOneBadACCEIEnvelope_goodCount (threshold : ℕ) :
    acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold = 1 := by
  classical
  unfold acceiGoodCount
  have hfilter :
      (Finset.univ.filter fun b : Bool =>
        oneGoodOneBadACCEIEnvelope threshold b ≤ threshold) = {false} := by
    ext b
    cases b <;> simp [oneGoodOneBadACCEIEnvelope]
  rw [hfilter]
  simp

/-- The sharp two-coordinate envelope has exactly one bad coordinate. -/
theorem oneGoodOneBadACCEIEnvelope_badCount (threshold : ℕ) :
    acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold = 1 := by
  classical
  unfold acceiBadCount
  have hfilter :
      (Finset.univ.filter fun b : Bool =>
        threshold < oneGoodOneBadACCEIEnvelope threshold b) = {true} := by
    ext b
    cases b <;> simp [oneGoodOneBadACCEIEnvelope]
  rw [hfilter]
  simp

/-- The finite Markov bad-coordinate inequality is sharp on the
one-good/one-bad envelope. -/
theorem oneGoodOneBadACCEIEnvelope_markov_badCount_sharp (threshold : ℕ) :
    acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
        (threshold + 1) =
      ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b := by
  rw [oneGoodOneBadACCEIEnvelope_badCount, oneGoodOneBadACCEIEnvelope_sum]
  simp

/-- The division-form good-coordinate lower bound is also sharp on the
one-good/one-bad envelope. -/
theorem oneGoodOneBadACCEIEnvelope_good_lower_bound_sharp (threshold : ℕ) :
    Fintype.card Bool - (threshold + 1) / (threshold + 1) =
      acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold := by
  have hdiv : (threshold + 1) / (threshold + 1) = 1 :=
    Nat.div_self (Nat.succ_pos threshold)
  simp [oneGoodOneBadACCEIEnvelope_goodCount, hdiv]

/-- The sharp envelope satisfies the averaged budget but not the conclusion
that every coordinate survives pruning. -/
theorem oneGoodOneBadACCEIEnvelope_not_all_good (threshold : ℕ) :
    ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold := by
  intro hgood
  have hbad := hgood true
  simp [oneGoodOneBadACCEIEnvelope] at hbad

/-- If the whole envelope is below `threshold + 1`, every coordinate is in the
pruned good set. -/
theorem all_accei_good_of_sum_lt_succ_threshold
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold : ℕ)
    (hsum : (∑ i, η i) < threshold + 1) :
    ∀ i : ι, η i ≤ threshold := by
  intro i
  by_contra hle
  have hlt : threshold < η i := by omega
  have hsingle : threshold + 1 ≤ η i := Nat.succ_le_of_lt hlt
  have hterm : η i ≤ ∑ j, η j := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- A one-step count bound with rate `numerator / denominator` relative to an
existing finite history. -/
def PrefixRateStep {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω)
    (numerator denominator : ℕ) : Prop :=
  denominator * finiteHistoryCount Ω (hist ++ [E]) ≤
    numerator * finiteHistoryCount Ω hist

/-- Sequential one-step rate admissibility from an existing finite history. -/
def SequentialRateAdmissibleFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) :
    List (FiniteEvent Ω) → ℕ → ℕ → Prop
  | [], _numerator, _denominator => True
  | E :: rest, numerator, denominator =>
      PrefixRateStep hist E numerator denominator ∧
        SequentialRateAdmissibleFrom (hist ++ [E]) rest numerator denominator

/-- Sequential one-step rate admissibility from the empty public history. -/
def SequentialRateAdmissible {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω)) (numerator denominator : ℕ) : Prop :=
  SequentialRateAdmissibleFrom ([] : List (FiniteEvent Ω))
    events numerator denominator

/-- The first step of a sequential rate proof is its prefix rate step. -/
theorem prefixRateStep_of_sequentialRateAdmissibleFrom_cons
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    {numerator denominator : ℕ}
    (h : SequentialRateAdmissibleFrom hist (E :: rest) numerator denominator) :
    PrefixRateStep hist E numerator denominator := by
  exact h.1

/-- A failed one-step rate bound blocks the corresponding sequential rate
admissibility proof. -/
theorem not_sequentialRateAdmissibleFrom_cons_of_not_prefixRateStep
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {E : FiniteEvent Ω}
    {numerator denominator : ℕ}
    (hfail : ¬ PrefixRateStep hist E numerator denominator) :
    ¬ SequentialRateAdmissibleFrom hist (E :: rest) numerator denominator := by
  intro h
  exact hfail (prefixRateStep_of_sequentialRateAdmissibleFrom_cons h)

/-- Generic finite tower-product count bound for an arbitrary one-step rate
`numerator / denominator`. -/
theorem finiteHistory_product_bound_of_sequentialRateFrom
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω)) (numerator denominator : ℕ)
    (h : SequentialRateAdmissibleFrom hist rest numerator denominator) :
    denominator ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
      numerator ^ rest.length * finiteHistoryCount Ω hist := by
  induction rest generalizing hist with
  | nil =>
      simp
  | cons E rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have ih' := ih (hist ++ [E]) hrest
      have hleft :
          denominator *
              (denominator ^ rest.length *
                finiteHistoryCount Ω ((hist ++ [E]) ++ rest)) ≤
            denominator *
              (numerator ^ rest.length *
                finiteHistoryCount Ω (hist ++ [E])) :=
        Nat.mul_le_mul_left denominator ih'
      have hright :
          numerator ^ rest.length *
              (denominator * finiteHistoryCount Ω (hist ++ [E])) ≤
            numerator ^ rest.length *
              (numerator * finiteHistoryCount Ω hist) :=
        Nat.mul_le_mul_left (numerator ^ rest.length) hstep
      calc
        denominator ^ (E :: rest).length *
            finiteHistoryCount Ω (hist ++ E :: rest)
            = denominator *
                (denominator ^ rest.length *
              finiteHistoryCount Ω ((hist ++ [E]) ++ rest)) := by
              rw [finiteHistoryCount_append_cons]
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
        _ ≤ denominator *
              (numerator ^ rest.length *
                finiteHistoryCount Ω (hist ++ [E])) := hleft
        _ = numerator ^ rest.length *
              (denominator * finiteHistoryCount Ω (hist ++ [E])) := by
              rw [Nat.mul_left_comm]
        _ ≤ numerator ^ rest.length *
              (numerator * finiteHistoryCount Ω hist) := hright
        _ = numerator ^ (E :: rest).length * finiteHistoryCount Ω hist := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Empty-history form of the finite tower-product count bound. -/
theorem finiteHistory_product_bound_of_sequentialRate
    {Ω : Type u} [Fintype Ω]
    (events : List (FiniteEvent Ω)) (numerator denominator : ℕ)
    (h : SequentialRateAdmissible events numerator denominator) :
    denominator ^ events.length * finiteHistoryCount Ω events ≤
      numerator ^ events.length *
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  exact finiteHistory_product_bound_of_sequentialRateFrom
    ([] : List (FiniteEvent Ω)) events numerator denominator h

/-- Contrapositive form: a product-bound violation exposes failure of the
sequential one-step rate proof. -/
theorem not_sequentialRateAdmissibleFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist rest : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ rest.length * finiteHistoryCount Ω (hist ++ rest) ≤
        numerator ^ rest.length * finiteHistoryCount Ω hist) :
    ¬ SequentialRateAdmissibleFrom hist rest numerator denominator := by
  intro h
  exact hbad
    (finiteHistory_product_bound_of_sequentialRateFrom
      hist rest numerator denominator h)

/-- Empty-history contrapositive of the finite tower-product count bound. -/
theorem not_sequentialRateAdmissible_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ events.length * finiteHistoryCount Ω events ≤
        numerator ^ events.length *
          finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ SequentialRateAdmissible events numerator denominator := by
  exact not_sequentialRateAdmissibleFrom_of_product_bound_violation hbad

/-- Failure of recursive sequential rate admissibility localizes to one failed
prefix rate step, with the current history extended by exactly the preceding
events. -/
theorem exists_failed_prefixRateStep_at_append_cons_of_not_sequentialRateAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hfail : ¬ SequentialRateAdmissibleFrom hist events numerator denominator) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep (hist ++ pre) E numerator denominator := by
  induction events generalizing hist with
  | nil =>
      exact False.elim (hfail trivial)
  | cons E rest ih =>
      by_cases hstep : PrefixRateStep hist E numerator denominator
      · have htail :
            ¬ SequentialRateAdmissibleFrom (hist ++ [E]) rest
              numerator denominator := by
          intro hrest
          exact hfail ⟨hstep, hrest⟩
        rcases ih (hist := hist ++ [E]) htail with
          ⟨pre, F, suffix, hevents, hbad⟩
        refine ⟨E :: pre, F, suffix, ?_, ?_⟩
        · simp [hevents]
        · simpa [List.append_assoc] using hbad
      · refine ⟨[], E, rest, ?_, ?_⟩
        · simp
        · simpa using hstep

/-- A tower-product violation localizes to a concrete failed prefix rate step. -/
theorem exists_failed_prefixRateStep_at_append_cons_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ events.length *
            finiteHistoryCount Ω (hist ++ events) ≤
          numerator ^ events.length * finiteHistoryCount Ω hist) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep (hist ++ pre) E numerator denominator := by
  exact
    exists_failed_prefixRateStep_at_append_cons_of_not_sequentialRateAdmissibleFrom
      (not_sequentialRateAdmissibleFrom_of_product_bound_violation hbad)

/-- Empty-history form: a product-bound violation gives an exact failed
conditional prefix rate step. -/
theorem exists_failed_prefixRateStep_at_append_cons_of_empty_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {events : List (FiniteEvent Ω)} {numerator denominator : ℕ}
    (hbad :
      ¬ denominator ^ events.length * finiteHistoryCount Ω events ≤
        numerator ^ events.length *
          finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ∃ pre E suffix,
      events = pre ++ E :: suffix ∧
        ¬ PrefixRateStep pre E numerator denominator := by
  simpa [SequentialRateAdmissible] using
    exists_failed_prefixRateStep_at_append_cons_of_product_bound_violation
      (Ω := Ω) (hist := ([] : List (FiniteEvent Ω)))
      (events := events) (numerator := numerator)
      (denominator := denominator) hbad

/-- The existing half-step interface is the special case `numerator = 1`,
`denominator = 2` of the general rate interface. -/
theorem sequentialRateAdmissibleFrom_one_two_of_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    (hist rest : List (FiniteEvent Ω))
    (h : SequentialHalfAdmissibleFrom hist rest) :
    SequentialRateAdmissibleFrom hist rest 1 2 := by
  induction rest generalizing hist with
  | nil =>
      trivial
  | cons E rest ih =>
      exact ⟨by simpa [PrefixRateStep] using h.1, ih (hist ++ [E]) h.2⟩

end Mettapedia.Computability.PNP
