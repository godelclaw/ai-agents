import Mettapedia.Computability.PNP.FiniteCoinSourceErasureFoundation

/-!
# P vs NP grassroots: finite-coin erasure as finite-count independence

`FiniteCoinSourceErasureFoundation` records the output-side meaning of balanced
finite-coin fibers: every decidable output predicate is source-neutral, and
Boolean decoders are exactly half-accurate.

This file connects that output-side API back to the finite-count conditional
independence API.  On the two-sided sample space `Bool × Coin`, predicate
neutrality is exactly exact finite-count independence between the source bit and
the corresponding output predicate, conditioned on the whole sample space.
-/

namespace Mettapedia.Computability.PNP

/-- The source-true event on the two-sided finite-coin sample space. -/
def finiteCoinSourceTrue {Coin : Type*} (ω : Bool × Coin) : Prop :=
  ω.1 = true

instance finiteCoinSourceTrue_decidablePred {Coin : Type*} :
    DecidablePred (finiteCoinSourceTrue (Coin := Coin)) :=
  fun ω => inferInstanceAs (Decidable (ω.1 = true))

/-- The output variable induced by a finite-coin recoding on the two-sided
sample space. -/
def finiteCoinOutput {Coin α : Type*} (r : Bool → Coin → α) :
    Bool × Coin → α :=
  fun ω => r ω.1 ω.2

private theorem finiteEventCount_eq_of_iff_bridge
    {Ω : Type*} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  exact le_antisymm
    (finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE))
    (finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF))

private theorem finiteEventCount_eq_zero_of_card_eq_zero
    {Ω : Type*} [Fintype Ω]
    (E : Ω → Prop) [DecidablePred E]
    (hcard : Fintype.card Ω = 0) :
    finiteEventCount Ω E = 0 := by
  have hle : finiteEventCount Ω E ≤ finiteEventCount Ω (fun _ω => True) :=
    finiteEventCount_le_of_imp (fun _ω _hE => trivial)
  have hall : finiteEventCount Ω (fun _ω => True) = Fintype.card Ω := by
    simp [finiteEventCount]
  omega

/-- The whole two-sided finite-coin sample space has size `2 * |Coin|`. -/
theorem finiteCoinSampleSpace_count
    {Coin : Type*} [Fintype Coin] :
    finiteEventCount (Bool × Coin) (fun _ω => True) =
      2 * Fintype.card Coin := by
  simp [finiteEventCount]

/-- The source-true side of the two-sided finite-coin sample space has size
`|Coin|`. -/
theorem finiteCoinSourceTrue_count
    {Coin : Type*} [Fintype Coin] :
    finiteEventCount (Bool × Coin) (finiteCoinSourceTrue (Coin := Coin)) =
      Fintype.card Coin := by
  simpa [finiteCoinSourceTrue, finiteEventCount] using
    finiteEventCount_prod
      (Ω := Bool) (Coin := Coin)
      (fun b : Bool => b = true) (fun _c : Coin => True)

/-- Counting a true-source output predicate on `Bool × Coin` reduces to the
true-side coin count. -/
theorem finiteCoinSourceTrue_outputPredicate_count
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    finiteEventCount (Bool × Coin)
        (fun ω => finiteCoinSourceTrue (Coin := Coin) ω ∧ P (finiteCoinOutput r ω)) =
      finiteEventCount Coin (fun c => P (r true c)) := by
  have hrect :
      finiteEventCount (Bool × Coin)
          (fun ω => ω.1 = true ∧ P (r true ω.2)) =
        finiteEventCount Bool (fun b : Bool => b = true) *
          finiteEventCount Coin (fun c => P (r true c)) :=
    finiteEventCount_prod
      (Ω := Bool) (Coin := Coin)
      (fun b : Bool => b = true) (fun c : Coin => P (r true c))
  have hcongr :
      finiteEventCount (Bool × Coin)
          (fun ω => finiteCoinSourceTrue (Coin := Coin) ω ∧ P (finiteCoinOutput r ω)) =
        finiteEventCount (Bool × Coin)
          (fun ω => ω.1 = true ∧ P (r true ω.2)) := by
    exact finiteEventCount_eq_of_iff_bridge (Ω := Bool × Coin) (fun ω => by
      constructor
      · intro h
        have hs : ω.1 = true := by
          simpa [finiteCoinSourceTrue] using h.1
        exact And.intro hs (by simpa [finiteCoinOutput, hs] using h.2)
      · intro h
        exact And.intro (by simpa [finiteCoinSourceTrue] using h.1)
          (by simpa [finiteCoinOutput, h.1] using h.2))
  rw [hcongr]
  simpa [finiteEventCount] using hrect

private noncomputable def finiteCoinOutputPredicateSplitEquiv
    {Coin α : Type*}
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    {ω : Bool × Coin // P (finiteCoinOutput r ω)} ≃
      ({c : Coin // P (r true c)} ⊕ {c : Coin // P (r false c)}) where
  toFun ω :=
    match h : ω.1.1 with
    | true => Sum.inl ⟨ω.1.2, by simpa [finiteCoinOutput, h] using ω.2⟩
    | false => Sum.inr ⟨ω.1.2, by simpa [finiteCoinOutput, h] using ω.2⟩
  invFun ω :=
    match ω with
    | Sum.inl c => ⟨(true, c.1), by simpa [finiteCoinOutput] using c.2⟩
    | Sum.inr c => ⟨(false, c.1), by simpa [finiteCoinOutput] using c.2⟩
  left_inv ω := by
    rcases ω with ⟨⟨b, c⟩, hP⟩
    cases b <;> simp
  right_inv ω := by
    cases ω with
    | inl c =>
        rcases c with ⟨c, hP⟩
        simp
    | inr c =>
        rcases c with ⟨c, hP⟩
        simp

/-- Counting an output predicate on the two-sided sample space splits into its
true-side and false-side coin counts. -/
theorem finiteCoinOutputPredicate_count
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    finiteEventCount (Bool × Coin) (fun ω => P (finiteCoinOutput r ω)) =
      finiteEventCount Coin (fun c => P (r true c)) +
        finiteEventCount Coin (fun c => P (r false c)) := by
  classical
  simpa [finiteEventCount, Fintype.card_sum] using
    Fintype.card_congr (finiteCoinOutputPredicateSplitEquiv r P)

/-- A neutral output predicate is exactly independent of the source bit on the
two-sided finite-coin sample space. -/
theorem countIndependentWithin_trueSource_outputPredicate_of_finiteCoinOutputPredicateNeutral
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hneutral : finiteCoinOutputPredicateNeutral r P) :
    CountIndependentWithin (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (fun ω => P (finiteCoinOutput r ω)) := by
  let n := Fintype.card Coin
  let t := finiteEventCount Coin (fun c => P (r true c))
  let f := finiteEventCount Coin (fun c => P (r false c))
  have hneutral' : t = f := by
    simpa [t, f, finiteCoinOutputPredicateNeutral] using hneutral
  have harith : (2 * n) * t = n * (t + f) := by
    rw [hneutral']
    ring
  simpa [CountIndependentWithin, finiteCoinSampleSpace_count,
    finiteCoinSourceTrue_count, finiteCoinSourceTrue_outputPredicate_count,
    finiteCoinOutputPredicate_count, n, t, f] using harith

/-- Predicate erasure makes every decidable output predicate exactly independent
of the source bit on the two-sided finite-coin sample space. -/
theorem countIndependentWithin_trueSource_outputPredicate_of_outputPredicateErasing
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (herase : FiniteCoinOutputPredicateErasing r) :
    CountIndependentWithin (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (fun ω => P (finiteCoinOutput r ω)) :=
  countIndependentWithin_trueSource_outputPredicate_of_finiteCoinOutputPredicateNeutral
    r P (herase P)

/-- Exact finite-count independence of an output predicate from the source bit
forces predicate neutrality. -/
theorem finiteCoinOutputPredicateNeutral_of_countIndependentWithin_trueSource_outputPredicate
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hind : CountIndependentWithin (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (fun ω => P (finiteCoinOutput r ω))) :
    finiteCoinOutputPredicateNeutral r P := by
  let n := Fintype.card Coin
  let t := finiteEventCount Coin (fun c => P (r true c))
  let f := finiteEventCount Coin (fun c => P (r false c))
  have hind' : (2 * n) * t = n * (t + f) := by
    simpa [CountIndependentWithin, finiteCoinSampleSpace_count,
      finiteCoinSourceTrue_count, finiteCoinSourceTrue_outputPredicate_count,
      finiteCoinOutputPredicate_count, n, t, f] using hind
  by_cases hn : n = 0
  · have ht : t = 0 := by
      exact finiteEventCount_eq_zero_of_card_eq_zero
        (fun c => P (r true c)) (by simpa [n] using hn)
    have hf : f = 0 := by
      exact finiteEventCount_eq_zero_of_card_eq_zero
        (fun c => P (r false c)) (by simpa [n] using hn)
    simp [finiteCoinOutputPredicateNeutral, t, f, ht, hf]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hcancel : 2 * t = t + f := by
      apply Nat.mul_left_cancel hnpos
      calc
        n * (2 * t) = (2 * n) * t := by ring
        _ = n * (t + f) := hind'
    have htf : t = f := by omega
    simpa [finiteCoinOutputPredicateNeutral, t, f] using htf

/-- Predicate neutrality is exactly exact finite-count independence from the
source bit on `Bool × Coin`. -/
theorem finiteCoinOutputPredicateNeutral_iff_countIndependentWithin_trueSource_outputPredicate
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P] :
    finiteCoinOutputPredicateNeutral r P ↔
      CountIndependentWithin (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => P (finiteCoinOutput r ω)) := by
  constructor
  · exact countIndependentWithin_trueSource_outputPredicate_of_finiteCoinOutputPredicateNeutral
      r P
  · exact finiteCoinOutputPredicateNeutral_of_countIndependentWithin_trueSource_outputPredicate
      r P

/-- Predicate erasure is exactly independence of every decidable output
predicate from the source bit on the two-sided finite-coin sample space. -/
theorem finiteCoinOutputPredicateErasing_iff_forall_countIndependentWithin_trueSource_outputPredicate
    {Coin α : Type*} [Fintype Coin]
    (r : Bool → Coin → α) :
    FiniteCoinOutputPredicateErasing r ↔
      ∀ P : α → Prop, [DecidablePred P] →
        CountIndependentWithin (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (fun ω => P (finiteCoinOutput r ω)) := by
  constructor
  · intro herase P _hP
    exact countIndependentWithin_trueSource_outputPredicate_of_outputPredicateErasing
      r P herase
  · intro h P _hP
    exact finiteCoinOutputPredicateNeutral_of_countIndependentWithin_trueSource_outputPredicate
      r P (h P)

/-- Balanced finite-coin fibers are exactly zero-tolerance output independence
of the induced output variable from the source bit. -/
theorem finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) 0 := by
  constructor
  · intro hbal y
    have herase := finiteCoinOutputPredicateErasing_of_fiberBalanced r hbal
    exact (countIndependentWithinTolerance_zero_iff_countIndependentWithin
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (fun ω => finiteCoinOutput r ω = y)).mpr
        (countIndependentWithin_trueSource_outputPredicate_of_outputPredicateErasing
          r (fun z => z = y) herase)
  · intro h y
    have hind :
        CountIndependentWithin (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (fun ω => finiteCoinOutput r ω = y) :=
      (countIndependentWithinTolerance_zero_iff_countIndependentWithin
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y)).mp (h y)
    have hneutral :=
      finiteCoinOutputPredicateNeutral_of_countIndependentWithin_trueSource_outputPredicate
        r (fun z => z = y) hind
    simpa [finiteCoinOutputPredicateNeutral, coinTrueFiberCount,
      coinFalseFiberCount] using hneutral

/-- For finite output types, balanced finite-coin fibers are exactly zero maximum
finite-count output defect between the source bit and the induced output
variable. -/
theorem finiteCoinRecodingFiberBalanced_iff_countIndependentWithinOutputDefect_eq_zero
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) = 0 := by
  exact (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
    r).trans (by
      simpa using
        (countIndependentWithinToleranceOutput_iff_outputDefect_le
          (fun _ω : Bool × Coin => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) 0))

end Mettapedia.Computability.PNP
