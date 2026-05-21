import Mettapedia.Computability.PNP.ConditioningObstruction

/-!
# P vs NP crux: approximate decorrelation has a finite-count lower bound

The exact conditioning obstruction says that deterministic coupling or
anti-coupling inside a conditioning event destroys the cross-multiplied
finite-count independence equation unless the conditioned source bit is
degenerate.  This file records the quantitative version needed to audit
``approximate decorrelation'' repairs.

Instead of merely saying that exact independence fails, we define the two
oriented natural-number defects of the cross-multiplied equation.  A coupled
conditioned bit has forward defect exactly
`#(C ∩ E) * #(C ∩ ¬ E)`, while an anti-coupled bit has the same product as
backward defect.  Any approximate replacement must therefore bound this
explicit product; it cannot repair the conditioning step by renaming exact
independence as approximate independence.
-/

namespace Mettapedia.Computability.PNP

/-- The forward oriented defect of the conditional finite-count independence
equation.  It is zero when the left cross product is no larger than the right
cross product, and otherwise records the natural-number excess. -/
def countIndependentWithinForwardGap {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    Nat :=
  finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) -
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω)

/-- The backward oriented defect of the conditional finite-count independence
equation.  Together with the forward defect, this gives a division-free
finite-count notion of symmetric tolerance around exact independence. -/
def countIndependentWithinBackwardGap {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    Nat :=
  finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω) -
    finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω)

/-- Symmetric finite-count approximate conditional independence with tolerance
`τ`: both oriented cross-multiplied defects are bounded by `τ`. -/
def CountIndependentWithinTolerance {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) : Prop :=
  countIndependentWithinForwardGap (Ω := Ω) C E F ≤ τ ∧
    countIndependentWithinBackwardGap (Ω := Ω) C E F ≤ τ

/-- Output-variable form of symmetric finite-count approximate conditional
independence: every decidable output fiber of `Y` is independent of `E` inside
`C`, up to the same tolerance `τ`.  This prevents a repair from hiding an
informative recoding by certifying only the aggregate output variable. -/
def CountIndependentWithinToleranceOutput {Ω α : Type*} [Fintype Ω]
    [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat) : Prop :=
  ∀ y : α, CountIndependentWithinTolerance (Ω := Ω) C E (fun ω => Y ω = y) τ

/-- The product of the two source-bit fibers inside the conditioning event.
This is the exact finite-count obstruction term that an approximate
decorrelation theorem must dominate on coupled same-source surfaces. -/
def conditionedSourceFiberProduct {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] : Nat :=
  finiteEventCount Ω (fun ω => C ω ∧ E ω) *
    finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)

private noncomputable def approximateEventSplitEquiv {Ω : Type*}
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    {ω : Ω // C ω} ≃
      ({ω : Ω // C ω ∧ E ω} ⊕ {ω : Ω // C ω ∧ ¬ E ω}) where
  toFun ω :=
    if hE : E ω.1 then Sum.inl ⟨ω.1, ⟨ω.2, hE⟩⟩
    else Sum.inr ⟨ω.1, ⟨ω.2, hE⟩⟩
  invFun ω :=
    match ω with
    | Sum.inl h => ⟨h.1, h.2.1⟩
    | Sum.inr h => ⟨h.1, h.2.1⟩
  left_inv ω := by
    rcases ω with ⟨ω, hC⟩
    by_cases hE : E ω <;> simp [hE]
  right_inv ω := by
    cases ω with
    | inl h =>
        rcases h with ⟨ω, hC, hE⟩
        simp [hE]
    | inr h =>
        rcases h with ⟨ω, hC, hE⟩
        simp [hE]

private theorem finiteEventCount_split_by_approximate {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    finiteEventCount Ω C =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  simpa [finiteEventCount, Fintype.card_sum] using
    Fintype.card_congr (approximateEventSplitEquiv C E)

private theorem finiteEventCount_congr_approximate {Ω : Type*} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  exact le_antisymm
    (finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE))
    (finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF))

private noncomputable def fstLiftEventEquiv {Ω Coin : Type*}
    (P : Ω → Prop) [DecidablePred P] :
    {xr : Ω × Coin // P xr.1} ≃ ({ω : Ω // P ω} × Coin) where
  toFun xr := (⟨xr.1.1, xr.2⟩, xr.1.2)
  invFun pc := ⟨(pc.1.1, pc.2), pc.1.2⟩
  left_inv xr := by
    rcases xr with ⟨⟨ω, c⟩, hP⟩
    rfl
  right_inv pc := by
    rcases pc with ⟨⟨ω, hP⟩, c⟩
    rfl

/-- Counting a source-only event on a source/coin product factors as the source
event count times the number of coins. -/
theorem finiteEventCount_fst_lift
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) [DecidablePred P] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1) =
      finiteEventCount Ω P * Fintype.card Coin := by
  classical
  simpa [finiteEventCount] using
    Fintype.card_congr (fstLiftEventEquiv (Ω := Ω) (Coin := Coin) P)

/-- Source-only positivity lifts to a source/coin product as soon as the finite
coin space is nonempty. -/
theorem finiteEventCount_fst_lift_pos_of_pos
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    (P : Ω → Prop) [DecidablePred P]
    (hpos : 0 < finiteEventCount Ω P) :
    0 < finiteEventCount (Ω × Coin) (fun xr => P xr.1) := by
  rw [finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) P]
  exact Nat.mul_pos hpos Fintype.card_pos

private noncomputable def prodEventEquiv {Ω Coin : Type*}
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    {xr : Ω × Coin // P xr.1 ∧ Q xr.2} ≃
      ({ω : Ω // P ω} × {c : Coin // Q c}) where
  toFun xr := (⟨xr.1.1, xr.2.1⟩, ⟨xr.1.2, xr.2.2⟩)
  invFun pc := ⟨(pc.1.1, pc.2.1), pc.1.2, pc.2.2⟩
  left_inv xr := by
    rcases xr with ⟨⟨ω, c⟩, hP, hQ⟩
    rfl
  right_inv pc := by
    rcases pc with ⟨⟨ω, hP⟩, ⟨c, hQ⟩⟩
    rfl

/-- Counting a rectangular event on a finite product factors as the product of
the two event counts. -/
theorem finiteEventCount_prod
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1 ∧ Q xr.2) =
      finiteEventCount Ω P * finiteEventCount Coin Q := by
  classical
  simpa [finiteEventCount] using
    Fintype.card_congr (prodEventEquiv (Ω := Ω) (Coin := Coin) P Q)

/-- Number of coin values for which an output fiber `y` is selected when the
source bit is `true`. -/
def coinTrueFiberCount {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) : Nat :=
  finiteEventCount Coin (fun c => r true c = y)

/-- Number of coin values for which an output fiber `y` is selected when the
source bit is `false`. -/
def coinFalseFiberCount {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) : Nat :=
  finiteEventCount Coin (fun c => r false c = y)

/-- A finite-coin recoding has balanced output fibers when every output value
appears equally often on the true and false source sides.  This is the exact
finite-count cancellation condition for the same-source randomized recoding
surface. -/
def FiniteCoinRecodingFiberBalanced {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) : Prop :=
  ∀ y : α, coinTrueFiberCount r y = coinFalseFiberCount r y

/-- The finite count of a singleton equality event is one. -/
theorem finiteEventCount_eq_self
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    finiteEventCount α (fun x => x = a) = 1 := by
  classical
  simp [finiteEventCount]

/-- If an event is pointwise false, its finite event count is zero. -/
theorem finiteEventCount_zero_of_forall_not
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P]
    (hfalse : ∀ ω, ¬ P ω) :
    finiteEventCount Ω P = 0 := by
  have hcongr :
      finiteEventCount Ω P = finiteEventCount Ω (fun _ω => False) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact False.elim (hfalse ω h)
      · intro h
        cases h)
  simpa [finiteEventCount] using hcongr

/-- Count the preimage of an output predicate by summing the counts of its
output fibers over any finite support containing the image of the map.  This is
the aggregate form needed for randomized recodings whose output type need not
itself be finite. -/
theorem finiteEventCount_comp_eq_sum_fibers_of_mapsTo
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Coin → α) (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hr : ∀ c : Coin, r c ∈ s) :
    finiteEventCount Coin (fun c => P (r c)) =
      ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y) := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset Coin))
    (t := (s.filter P : Finset α))
    (g := r)
  symm
  calc
    ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y)
        = ∑ y ∈ s.filter P,
            ((Finset.univ : Finset Coin).filter (fun c => r c = y)).card := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          simpa [finiteEventCount] using
            (Fintype.card_subtype (fun c : Coin => r c = y))
    _ = ((Finset.univ : Finset Coin).filter (fun c => r c ∈ s.filter P)).card := hfiber
    _ = finiteEventCount Coin (fun c => P (r c)) := by
          simpa [finiteEventCount, Finset.mem_filter, hr] using
            (Fintype.card_subtype (fun c : Coin => P (r c))).symm

/-- A Boolean-valued event partitions a finite type into its `true` and
`false` fibers. -/
theorem finiteEventCount_bool_true_add_false
    {Ω : Type*} [Fintype Ω] (B : Ω → Bool) :
    finiteEventCount Ω (fun ω => B ω = true) +
      finiteEventCount Ω (fun ω => B ω = false) = Fintype.card Ω := by
  have hsplit :=
    finiteEventCount_split_by_approximate (Ω := Ω)
      (fun _ω => True) (fun ω => B ω = true)
  have htruePart :
      finiteEventCount Ω (fun ω => True ∧ B ω = true) =
        finiteEventCount Ω (fun ω => B ω = true) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun _ω => by simp)
  have hfalsePart :
      finiteEventCount Ω (fun ω => True ∧ ¬ B ω = true) =
        finiteEventCount Ω (fun ω => B ω = false) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      cases B ω <;> simp)
  have htrueAll : finiteEventCount Ω (fun _ω => True) = Fintype.card Ω := by
    simp [finiteEventCount]
  rw [htrueAll, htruePart, hfalsePart] at hsplit
  exact hsplit.symm

/-- If `E` and `F` are coupled inside `C`, the forward approximate
decorrelation defect is exactly the product of the two conditioned source-bit
fibers. -/
theorem countIndependentWithinForwardGap_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    countIndependentWithinForwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
  simp only [countIndependentWithinForwardGap, hCEF, hCF, hsplit]
  rw [Nat.add_mul, Nat.add_sub_cancel_left, Nat.mul_comm]

/-- If `E` and `F` are anti-coupled inside `C`, the backward approximate
decorrelation defect is exactly the product of the two conditioned source-bit
fibers. -/
theorem countIndependentWithinBackwardGap_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    countIndependentWithinBackwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    have hfalse :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
          finiteEventCount Ω (fun _ω => False) := by
      exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact ((hanti ω h.1).1 h.2.1) h.2.2
        · intro h
          cases h)
    simpa [finiteEventCount] using hfalse
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        intro hE
        exact ((hanti ω h.1).1 hE) h.2
      · intro h
        refine ⟨h.1, ?_⟩
        by_contra hnotF
        exact h.2 ((hanti ω h.1).2 hnotF))
  simp [countIndependentWithinBackwardGap, hCEF, hCF]

/-- Nondegenerate coupled conditioning leaves a strictly positive forward
defect. -/
theorem countIndependentWithinForwardGap_pos_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinForwardGap (Ω := Ω) C E F := by
  rw [countIndependentWithinForwardGap_coupled C E F hcouple]
  exact Nat.mul_pos hpos hneg

/-- Nondegenerate anti-coupled conditioning leaves a strictly positive backward
defect. -/
theorem countIndependentWithinBackwardGap_pos_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinBackwardGap (Ω := Ω) C E F := by
  rw [countIndependentWithinBackwardGap_anticoupled C E F hanti]
  exact Nat.mul_pos hpos hneg

/-- A nondegenerate conditioned source bit has positive source-fiber product. -/
theorem conditionedSourceFiberProduct_pos_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact Nat.mul_pos hpos hneg

/-- Lower bounds on the two conditioned source-bit fibers multiply into a
lower bound on the source-fiber product. -/
theorem lowerBounds_mul_le_conditionedSourceFiberProduct
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    loTrue * loFalse ≤ conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact Nat.mul_le_mul htrue hfalse

/-- A coupled nondegenerate conditioning surface cannot satisfy a symmetric
approximate-independence tolerance smaller than the explicit source-fiber
product. -/
theorem not_countIndependentWithinTolerance_of_coupled_product_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  have hgap :
      countIndependentWithinForwardGap (Ω := Ω) C E F =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinForwardGap_coupled C E F hcouple
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.1)

/-- Obligation form of the coupled approximate-decorrelation blocker: any
successful symmetric tolerance certificate must dominate the source-fiber
product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_coupled_product_gt C E F τ hcouple
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Coupled obligation with explicit lower bounds: if both conditioned source
fibers have lower bounds, every approximate-independence tolerance certificate
must dominate the product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      C E F τ hcouple happrox)

/-- Coupled contradiction with explicit lower bounds: substantial mass on both
conditioned source-bit sides rules out any smaller symmetric tolerance. -/
theorem not_countIndependentWithinTolerance_of_coupled_lowerBounds_mul_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
      C E F τ loTrue loFalse hcouple htrue hfalse happrox)

/-- An anti-coupled nondegenerate conditioning surface cannot satisfy a
symmetric approximate-independence tolerance smaller than the explicit
source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_anticoupled_product_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  have hgap :
      countIndependentWithinBackwardGap (Ω := Ω) C E F =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinBackwardGap_anticoupled C E F hanti
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.2)

/-- Obligation form of the anti-coupled approximate-decorrelation blocker: any
successful symmetric tolerance certificate must dominate the source-fiber
product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_anticoupled_product_gt C E F τ hanti
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Anti-coupled obligation with explicit lower bounds: if both conditioned
source fibers have lower bounds, every approximate-independence tolerance
certificate must dominate the product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ hanti happrox)

/-- Anti-coupled contradiction with explicit lower bounds: substantial mass on
both conditioned source-bit sides rules out any smaller symmetric tolerance. -/
theorem not_countIndependentWithinTolerance_of_anticoupled_lowerBounds_mul_gt
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ loTrue loFalse hanti htrue hfalse happrox)

/-- The distinguishing true-side fiber of an arbitrary-codomain deterministic
recoding has the same forward product defect as a copied conditioned bit. -/
theorem countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true = y) (hf : r false ≠ y) :
    countIndependentWithinForwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  refine countIndependentWithinForwardGap_coupled C E
    (fun ω => r (decide (E ω)) = y) ?_
  intro ω _hC
  by_cases hE : E ω
  · simp [hE, ht]
  · simp [hE, hf]

/-- The distinguishing false-side fiber of an arbitrary-codomain deterministic
recoding has the same backward product defect as a complemented conditioned
bit. -/
theorem countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true ≠ y) (hf : r false = y) :
    countIndependentWithinBackwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  refine countIndependentWithinBackwardGap_anticoupled C E
    (fun ω => r (decide (E ω)) = y) ?_
  intro ω _hC
  by_cases hE : E ω
  · have hnotF : ¬ r (decide (E ω)) = y := by simpa [hE] using ht
    exact iff_of_true hE hnotF
  · have hF : r (decide (E ω)) = y := by simpa [hE] using hf
    exact iff_of_false hE (not_not.mpr hF)

/-- A true-side distinguishing fiber cannot satisfy a tolerance smaller than
the explicit source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true = y) (hf : r false ≠ y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  have hgap :
      countIndependentWithinForwardGap (Ω := Ω) C E
          (fun ω => r (decide (E ω)) = y) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
      C E r y ht hf
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.1)

/-- A false-side distinguishing fiber cannot satisfy a tolerance smaller than
the explicit source-fiber product. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true ≠ y) (hf : r false = y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  have hgap :
      countIndependentWithinBackwardGap (Ω := Ω) C E
          (fun ω => r (decide (E ω)) = y) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
    countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
      C E r y ht hf
  exact (Nat.not_le_of_gt htol) (by simpa [hgap] using happrox.2)

/-- Any deterministic output fiber that distinguishes the two source-bit values
inherits the same product lower bound on symmetric approximate independence. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  by_cases ht : r true = y
  · by_cases hf : r false = y
    · exact False.elim (hdistinguish (iff_of_true ht hf))
    · exact
        not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
          C E r y τ ht hf htol
  · by_cases hf : r false = y
    · exact
        not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
          C E r y τ ht hf htol
    · exact False.elim (hdistinguish (iff_of_false ht hf))

/-- Obligation form for deterministic recoding fibers: approximate
independence of any informative fiber forces the tolerance to dominate the
source-fiber product. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  by_contra hle
  have hgt : τ < conditionedSourceFiberProduct (Ω := Ω) C E := by omega
  exact
    (not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y τ hdistinguish
      (by simpa [conditionedSourceFiberProduct] using hgt)) happrox

/-- Deterministic distinguishing-fiber obligation with explicit lower bounds:
if both source-bit fibers have lower bounds, every approximate-independence
tolerance certificate for the informative output fiber must dominate the
product of those lower bounds. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ hdistinguish happrox)

/-- Deterministic distinguishing-fiber contradiction with explicit lower
bounds: substantial mass on both source-bit sides rules out any smaller
symmetric tolerance for an informative output fiber. -/
theorem not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_lowerBounds_mul_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ loTrue loFalse hdistinguish htrue hfalse happrox)

/-- Output-variable obligation for nonconstant deterministic recodings of the
conditioned bit.  If every output fiber is approximately independent with
tolerance `τ`, then `τ` must dominate the same source-fiber product; it is
enough to inspect the `r true` fiber. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  have hdistinguish : ¬ (r true = r true ↔ r false = r true) := by
    intro hiff
    exact hnonconst ((hiff.mp rfl).symm)
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r (r true) τ hdistinguish (happrox (r true))

/-- Output-variable lower-bound obligation for nonconstant deterministic
recodings: lower bounds on both conditioned source-bit sides force the shared
fiber tolerance to dominate their product. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct C E loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox)

/-- A nonconstant deterministic output variable cannot be approximately
independent of the source bit with tolerance below the explicit source-fiber
product. -/
theorem not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Lower-bound contradiction for output-variable approximate independence:
substantial mass on both source-bit sides rules out any smaller tolerance for a
nonconstant deterministic recoding. -/
theorem not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_lowerBounds_mul_gt
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ loTrue loFalse hnonconst htrue hfalse happrox)

/-- Count of the true-side part of an arbitrary finite-coin recoding fiber. -/
theorem finiteEventCount_finiteCoinRecoding_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
  have hcongr :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ E xr.1) ∧ r true xr.2 = y) := by
    exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, by simpa [h.2.1] using h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, by simpa [h.1.2] using h.2⟩)
  calc
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
        = finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ E xr.1) ∧ r true xr.2 = y) := hcongr
    _ = finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
          simpa [coinTrueFiberCount] using
            finiteEventCount_prod (Ω := Ω) (Coin := Coin)
              (fun ω => C ω ∧ E ω) (fun c => r true c = y)

/-- Count of the false-side part of an arbitrary finite-coin recoding fiber. -/
theorem finiteEventCount_finiteCoinRecoding_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  have hcongr :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ ¬ E xr.1) ∧ r false xr.2 = y) := by
    exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, by simpa [h.2.1] using h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, by simpa [h.1.2] using h.2⟩)
  calc
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
        = finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ ¬ E xr.1) ∧ r false xr.2 = y) := hcongr
    _ = finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
          simpa [coinFalseFiberCount] using
            finiteEventCount_prod (Ω := Ω) (Coin := Coin)
              (fun ω => C ω ∧ ¬ E ω) (fun c => r false c = y)

/-- Count of an arbitrary finite-coin recoding fiber, split by the source bit.
This is the finite-count surface where randomized recodings can cancel: only
the balance of the two coin fibers matters. -/
theorem finiteEventCount_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  have hsplit :=
    finiteEventCount_split_by_approximate
      (Ω := Ω × Coin)
      (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
      (fun xr => E xr.1)
  have htrue :
      finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
    have hcongr :
        finiteEventCount (Ω × Coin)
            (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ E xr.1) =
          finiteEventCount (Ω × Coin)
            (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) := by
      exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
    simpa [hcongr] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hfalse :
      finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
    have hcongr :
        finiteEventCount (Ω × Coin)
            (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ ¬ E xr.1) =
          finiteEventCount (Ω × Coin)
            (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) := by
      exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
    simpa [hcongr] using finiteEventCount_finiteCoinRecoding_falseFiber C E r y
  simpa [htrue, hfalse] using hsplit

/-- Exact forward defect for an arbitrary finite-coin recoding output fiber.
It is the source-fiber product times the number of coins times the positive
part of the true-minus-false coin-fiber imbalance. -/
theorem countIndependentWithinForwardGap_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  let A := finiteEventCount Ω (fun ω => C ω ∧ E ω)
  let B := finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)
  let N := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1) = (A + B) * N := by
    have hlift :=
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) C
    have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
    calc
      finiteEventCount (Ω × Coin) (fun xr => C xr.1)
          = finiteEventCount Ω C * Fintype.card Coin := hlift
      _ = (A + B) * N := by
            simp [A, B, N, hsplit]
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) = A * N := by
    simpa [A, N] using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCEF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧
            r (decide (E xr.1)) xr.2 = y) = A * T := by
    simpa [A, T] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hCF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        A * T + B * F := by
    simpa [A, B, T, F] using finiteEventCount_finiteCoinRecoding_fiber C E r y
  calc
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y)
        = ((A + B) * N) * (A * T) - (A * N) * (A * T + B * F) := by
          simp [countIndependentWithinForwardGap, hC, hCE, hCEF, hCF]
    _ = A * B * N * (T - F) := by
          calc
            ((A + B) * N) * (A * T) - (A * N) * (A * T + B * F)
                = (A * N) * ((A + B) * T) - (A * N) * (A * T + B * F) := by
                  ring_nf
            _ = (A * N) * (((A + B) * T) - (A * T + B * F)) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = (A * N) * ((A * T + B * T) - (A * T + B * F)) := by
                  ring_nf
            _ = (A * N) * (B * T - B * F) := by
                  rw [Nat.add_sub_add_left]
            _ = (A * N) * (B * (T - F)) := by
                  rw [← Nat.mul_sub_left_distrib B T F]
            _ = A * B * N * (T - F) := by
                  ring_nf

/-- Exact backward defect for an arbitrary finite-coin recoding output fiber.
It is the source-fiber product times the number of coins times the positive
part of the false-minus-true coin-fiber imbalance. -/
theorem countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  let A := finiteEventCount Ω (fun ω => C ω ∧ E ω)
  let B := finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)
  let N := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1) = (A + B) * N := by
    have hlift :=
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) C
    have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
    calc
      finiteEventCount (Ω × Coin) (fun xr => C xr.1)
          = finiteEventCount Ω C * Fintype.card Coin := hlift
      _ = (A + B) * N := by
            simp [A, B, N, hsplit]
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) = A * N := by
    simpa [A, N] using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCEF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧
            r (decide (E xr.1)) xr.2 = y) = A * T := by
    simpa [A, T] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hCF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        A * T + B * F := by
    simpa [A, B, T, F] using finiteEventCount_finiteCoinRecoding_fiber C E r y
  calc
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y)
        = (A * N) * (A * T + B * F) - ((A + B) * N) * (A * T) := by
          simp [countIndependentWithinBackwardGap, hC, hCE, hCEF, hCF]
    _ = A * B * N * (F - T) := by
          calc
            (A * N) * (A * T + B * F) - ((A + B) * N) * (A * T)
                = (A * N) * (A * T + B * F) - (A * N) * ((A + B) * T) := by
                  ring_nf
            _ = (A * N) * ((A * T + B * F) - ((A + B) * T)) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = (A * N) * ((A * T + B * F) - (A * T + B * T)) := by
                  ring_nf
            _ = (A * N) * (B * F - B * T) := by
                  rw [Nat.add_sub_add_left]
            _ = (A * N) * (B * (F - T)) := by
                  rw [← Nat.mul_sub_left_distrib B F T]
            _ = A * B * N * (F - T) := by
                  ring_nf

/-- Balanced finite-coin output fibers exactly decorrelate the marginal output
from the same source bit at zero tolerance.  This theorem is the formal
cancellation case: if every output value occurs equally often on the true and
false source sides, the output variable alone no longer carries finite-count
fiber evidence for `E`. -/
theorem countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  intro y
  constructor
  · rw [countIndependentWithinForwardGap_finiteCoinRecoding_fiber]
    simp [hbal y]
  · rw [countIndependentWithinBackwardGap_finiteCoinRecoding_fiber]
    simp [hbal y]

/-- The true-side fiber containing the output produced at a particular coin is
nonempty, hence has positive finite count. -/
theorem coinTrueFiberCount_self_pos
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    0 < coinTrueFiberCount r (r true c₀) := by
  unfold coinTrueFiberCount finiteEventCount
  exact Fintype.card_pos_iff.mpr ⟨⟨c₀, rfl⟩⟩

/-- A balanced finite-coin marginal recoding cannot have an output property
that separates the source bit at a particular coin.  If all true-side outputs
satisfy `P` and all false-side outputs fail `P`, the true-side fiber of
`r true c₀` is nonempty while the corresponding false-side fiber is empty,
contradicting balance. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) (c₀ : Coin)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  let y := r true c₀
  have hfalseEmpty : coinFalseFiberCount r y = 0 := by
    unfold coinFalseFiberCount
    exact finiteEventCount_zero_of_forall_not
      (fun c => r false c = y) (fun c hc => by
        exact hfalse c (by simpa [hc] using htrue c₀))
  have htrueZero : coinTrueFiberCount r y = 0 := by
    exact (hbal y).trans hfalseEmpty
  exact (Nat.ne_of_gt (coinTrueFiberCount_self_pos r c₀)) htrueZero

/-- Nonempty balanced finite-coin marginal recodings cannot have any
output-only predicate that separates the source bit uniformly on all coins. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r P c₀ htrue hfalse

/-- A balanced finite-coin marginal recoding cannot also have an output-only
Boolean decoder that recovers the source bit at a particular coin.  If the
decoder maps every true-side output to `true` and every false-side output to
`false`, the true-side fiber of `r true c₀` is nonempty while the corresponding
false-side fiber is empty, contradicting balance. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool) (c₀ : Coin)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r (fun y => decode y = true) c₀ htrue (fun c h => by
        have hdecodeFalse : decode (r false c) = false := hfalse c
        rw [h] at hdecodeFalse
        cases hdecodeFalse)

/-- Nonempty balanced finite-coin marginal recodings cannot have an output-only
Boolean decoder that recovers the source bit uniformly on all coins.  The only
way for balanced marginal fibers to decorrelate exactly is to erase such
output-only source evidence. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
      r decode c₀ htrue hfalse

/-- Balanced finite-coin marginal recodings give every output-only predicate
the same number of true-side and false-side coin witnesses.  Thus the balanced
escape can preserve only source-blind output statistics; any predicate-level
advantage for either source bit contradicts fiber balance. -/
theorem finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => P (r true c)) =
      finiteEventCount Coin (fun c => P (r false c)) := by
  classical
  let s : Finset α :=
    (Finset.univ.image (fun c : Coin => r true c)) ∪
      (Finset.univ.image (fun c : Coin => r false c))
  have htrueRange : ∀ c : Coin, r true c ∈ s := by
    intro c
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
  have hfalseRange : ∀ c : Coin, r false c ∈ s := by
    intro c
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
  rw [finiteEventCount_comp_eq_sum_fibers_of_mapsTo
        (fun c : Coin => r true c) s P htrueRange,
      finiteEventCount_comp_eq_sum_fibers_of_mapsTo
        (fun c : Coin => r false c) s P hfalseRange]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  simpa [coinTrueFiberCount, coinFalseFiberCount] using hbal y

/-- A true-side advantage for any decidable output predicate is incompatible
with balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_trueCount_gt_falseCount
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal)

/-- A false-side advantage for any decidable output predicate is incompatible
with balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_falseCount_gt_trueCount
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal).symm

/-- A balanced finite-coin marginal recoding gives every Boolean output
decoder exactly half aggregate accuracy across the two source sides.  Written
without division: the number of true-side coins decoded as `true` plus the
number of false-side coins decoded as `false` is exactly the coin count. -/
theorem finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => decode (r true c) = true) +
      finiteEventCount Coin (fun c => decode (r false c) = false) =
        Fintype.card Coin := by
  have hpred :=
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      r (fun y => decode y = true) hbal
  rw [hpred]
  exact finiteEventCount_bool_true_add_false (fun c => decode (r false c))

/-- Any Boolean output decoder with better-than-half aggregate accuracy across
the two source sides contradicts balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_correctCount_gt_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin <
      finiteEventCount Coin (fun c => decode (r true c) = true) +
        finiteEventCount Coin (fun c => decode (r false c) = false)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
      r decode hbal)

/-- Obligation form for an arbitrary finite-coin output fiber: approximate
output independence forces the tolerance to dominate the true-minus-false
coin-fiber imbalance, scaled by the source-fiber product and the number of
coins. -/
theorem trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber C E r y
  simpa [hgap] using (happrox y).1

/-- The corresponding obligation for the false-minus-true coin-fiber
imbalance. -/
theorem falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber C E r y
  simpa [hgap] using (happrox y).2

/-- Strict-tolerance blocker for an arbitrary finite-coin output fiber with
positive true-minus-false coin-fiber imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_trueMinusFalse_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Strict-tolerance blocker for an arbitrary finite-coin output fiber with
positive false-minus-true coin-fiber imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_falseMinusTrue_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound form of the true-minus-false mixed-coin obligation. -/
theorem sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (coinTrueFiberCount r y - coinFalseFiberCount r y)
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse)))
    (trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound form of the false-minus-true mixed-coin obligation. -/
theorem sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (coinFalseFiberCount r y - coinTrueFiberCount r y)
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse)))
    (falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound strict blocker for a positive true-minus-false
mixed-coin imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_trueMinusFalse_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox)

/-- Source lower-bound strict blocker for a positive false-minus-true
mixed-coin imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_falseMinusTrue_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox)

/-- If the tolerance is below one lower-bounded source/coin imbalance block,
then approximate output independence for a finite-coin recoding forces exact
balanced output fibers.  A nonzero true/false coin-fiber imbalance contributes
at least `loTrue * loFalse * |Coin|` defect. -/
theorem finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with htrue_lt_false | hfalse_lt_true
  · have hdiff_pos : 0 < coinFalseFiberCount r y - coinTrueFiberCount r y :=
      Nat.sub_pos_of_lt htrue_lt_false
    have hdiff_one : 1 ≤ coinFalseFiberCount r y - coinTrueFiberCount r y := hdiff_pos
    have hblock_le :
        loTrue * loFalse * Fintype.card Coin ≤
          loTrue * loFalse * Fintype.card Coin *
            (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
      calc
        loTrue * loFalse * Fintype.card Coin =
            loTrue * loFalse * Fintype.card Coin * 1 := by simp
        _ ≤
            loTrue * loFalse * Fintype.card Coin *
              (coinFalseFiberCount r y - coinTrueFiberCount r y) :=
          Nat.mul_le_mul_left (loTrue * loFalse * Fintype.card Coin) hdiff_one
    exact (Nat.not_le_of_gt hlt)
      (le_trans hblock_le
        (sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
          C E r y τ loTrue loFalse htrue hfalse happrox))
  · have hdiff_pos : 0 < coinTrueFiberCount r y - coinFalseFiberCount r y :=
      Nat.sub_pos_of_lt hfalse_lt_true
    have hdiff_one : 1 ≤ coinTrueFiberCount r y - coinFalseFiberCount r y := hdiff_pos
    have hblock_le :
        loTrue * loFalse * Fintype.card Coin ≤
          loTrue * loFalse * Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
      calc
        loTrue * loFalse * Fintype.card Coin =
            loTrue * loFalse * Fintype.card Coin * 1 := by simp
        _ ≤
            loTrue * loFalse * Fintype.card Coin *
              (coinTrueFiberCount r y - coinFalseFiberCount r y) :=
          Nat.mul_le_mul_left (loTrue * loFalse * Fintype.card Coin) hdiff_one
    exact (Nat.not_le_of_gt hlt)
      (le_trans hblock_le
        (sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
          C E r y τ loTrue loFalse htrue hfalse happrox))

/-- Below one lower-bounded source/coin imbalance block, approximate output
independence is equivalent to exact balanced fibers. -/
theorem countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro happrox
    exact
      finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
        C E r htrue hfalse happrox hlt
  · intro hbal y
    have hzero :=
      countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
        C E r hbal
    exact ⟨le_trans (hzero y).1 (Nat.zero_le τ),
      le_trans (hzero y).2 (Nat.zero_le τ)⟩

/-- Exact source-count form of finite-coin tolerance quantization: below the
first source-product times coin-count block, approximate output independence
forces exact balanced fibers. -/
theorem finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_sourceCoinProduct
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r le_rfl le_rfl happrox hlt

/-- Below the exact source-product times coin-count block, approximate output
independence is equivalent to exact balanced fibers. -/
theorem countIndependentWithinToleranceOutput_lt_sourceCoinProduct_iff_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r le_rfl le_rfl hlt

/-- Source-side nondegeneracy blocks zero-tolerance output independence for
any finite-coin output fiber with positive true-minus-false imbalance. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinFalseFiberCount r y < coinTrueFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_trueMinusFalse_gt
      C E r y 0 1 1 hpos hneg
  have hcoin : 0 < Fintype.card Coin := Fintype.card_pos
  have hdiff : 0 < coinTrueFiberCount r y - coinFalseFiberCount r y :=
    Nat.sub_pos_of_lt himb
  simpa using Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.one_pos Nat.one_pos) hcoin) hdiff

/-- Source-side nondegeneracy blocks zero-tolerance output independence for
any finite-coin output fiber with positive false-minus-true imbalance. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinTrueFiberCount r y < coinFalseFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_falseMinusTrue_gt
      C E r y 0 1 1 hpos hneg
  have hcoin : 0 < Fintype.card Coin := Fintype.card_pos
  have hdiff : 0 < coinFalseFiberCount r y - coinTrueFiberCount r y :=
    Nat.sub_pos_of_lt himb
  simpa using Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.one_pos Nat.one_pos) hcoin) hdiff

/-- On a source-side nondegenerate conditioned surface, exact zero-tolerance
finite-coin output independence is equivalent to balanced output fibers.  This
is the arbitrary finite-coin cancellation boundary: zero slack is possible
exactly when every output fiber has equal true-side and false-side coin counts. -/
theorem countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro happrox y
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact
        (not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
          C E r y hpos hneg hlt) happrox
    · exact
        (not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
          C E r y hpos hneg hgt) happrox
  · intro hbal
    exact countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
      C E r hbal

/-- If the random coin is retained together with the output, the true-side
fiber at a fixed coin has exactly one supporting coin value. -/
theorem coinTrueFiberCount_withCoin_trueFiber
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 1 := by
  have hcongr :
      finiteEventCount Coin
          (fun c => (r true c, c) = (r true c₀, c₀)) =
        finiteEventCount Coin (fun c => c = c₀) := by
    exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
      constructor
      · intro h
        exact congrArg Prod.snd h
      · intro h
        cases h
        rfl)
  exact hcongr.trans (finiteEventCount_eq_self c₀)

/-- If the retained-coin outputs at a fixed coin differ between the true and
false source sides, the matching false-side retained-coin fiber is empty. -/
theorem coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    coinFalseFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 0 := by
  unfold coinFalseFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r false c, c) = (r true c₀, c₀)) (fun c h => by
      have hc : c = c₀ := congrArg Prod.snd h
      subst c
      have hout : r false c₀ = r true c₀ := congrArg Prod.fst h
      exact hsep hout.symm)

/-- Exact forward defect for a retained-coin output fiber.  Balanced marginal
output fibers do not matter here: once the coin is retained, any coin at which
the true and false outputs differ exposes the source bit with the scaled
source-product defect. -/
theorem countIndependentWithinForwardGap_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, c)) (r true c₀, c₀)
  have htrue := coinTrueFiberCount_withCoin_trueFiber r c₀
  have hfalse := coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of the retained-coin output forces the tolerance
to dominate the source-product defect at any separated coin. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin ≤ τ := by
  have hgap := countIndependentWithinForwardGap_coinRetained_trueFiber C E r c₀ hsep
  have hcert :
      countIndependentWithinForwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) ≤ τ :=
    (happrox (r true c₀, c₀)).1
  rw [hgap] at hcert
  exact hcert

/-- Source lower-bound form of the retained-coin preservation obstruction. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
    (sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained-coin outputs: if the coin is kept,
any separated coin value preserves enough of the source bit to revive the
scaled finite-count obstruction. -/
theorem not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox)

/-- Source lower-bound strict-tolerance blocker for retained-coin outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse * Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ loTrue loFalse hsep htrue hfalse happrox)

/-- Retaining the coin turns balanced finite-coin fibers into pointwise
source-blindness at each coin.  Marginal balance can hide source information by
mixing over coins; once the coin itself is part of the certified output, exact
balance is possible only when the true and false outputs agree for every
retained coin value. -/
theorem finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) ↔
      ∀ c : Coin, r true c = r false c := by
  constructor
  · intro hbal c₀
    by_contra hsep
    have htrue := coinTrueFiberCount_withCoin_trueFiber r c₀
    have hfalse := coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep
    have hfiber := hbal (r true c₀, c₀)
    simp [htrue, hfalse] at hfiber
  · intro hpoint y
    unfold coinTrueFiberCount coinFalseFiberCount
    exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
      have hpair : (r true c, c) = (r false c, c) :=
        Prod.ext (hpoint c) rfl
      constructor
      · intro h
        change (r false c, c) = y
        rw [← hpair]
        exact h
      · intro h
        change (r true c, c) = y
        rw [hpair]
        exact h)

/-- Source lower-bound retained-coin quantization: below one lower-bounded
source/coin block, approximate independence of the output that retains the
coin is equivalent to pointwise source-blindness at every retained coin. -/
theorem countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => (r b c, c)) htrue hfalse hlt
    _ ↔ ∀ c : Coin, r true c = r false c :=
          finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq r

/-- Exact source-count specialization of retained-coin quantization. -/
theorem countIndependentWithinToleranceOutput_coinRetained_lt_sourceCoinProduct_iff_pointwise_eq
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
      C E r le_rfl le_rfl hlt

/-- For a retained side channel, a true pair fiber is the simultaneous output
and side equality class on the true source side. -/
theorem coinTrueFiberCount_withSide
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (y : α) (s : Side) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) =
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) := by
  unfold coinTrueFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- For a retained side channel, a false pair fiber is the simultaneous output
and side equality class on the false source side. -/
theorem coinFalseFiberCount_withSide
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (y : α) (s : Side) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) =
      finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  unfold coinFalseFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- Retaining an arbitrary side channel turns balanced recoding fibers into
side-fiber balance: for every certified output and retained side value, the
true and false coin counts inside that side fiber must agree. -/
theorem finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) ↔
      ∀ (y : α) (s : Side),
        finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  constructor
  · intro hbal y s
    calc
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) := by
        exact (coinTrueFiberCount_withSide r side y s).symm
      _ = coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) :=
        hbal (y, s)
      _ = finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
        exact coinFalseFiberCount_withSide r side y s
  · intro hside ys
    rcases ys with ⟨y, s⟩
    calc
      coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) =
          finiteEventCount Coin (fun c => r true c = y ∧ side c = s) := by
        exact coinTrueFiberCount_withSide r side y s
      _ = finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
        hside y s
      _ = coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) := by
        exact (coinFalseFiberCount_withSide r side y s).symm

/-- Source lower-bound retained-side quantization: below one lower-bounded
source/coin block, approximate independence of the output retaining side
information is equivalent to exact true/false balance inside every
output/side fiber. -/
theorem countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => (r b c, side c)) htrue hfalse hlt
    _ ↔ ∀ (y : α) (s : Side),
          finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
            finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
          finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq r side

/-- Exact source-count specialization of retained-side quantization. -/
theorem countIndependentWithinToleranceOutput_sideRetained_lt_sourceCoinProduct_iff_sideFiber_count_eq
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
      C E r side le_rfl le_rfl hlt

/-- For a retained side channel, the true-side fiber at a fixed side value is
the true output/side equality class.  This generalizes the retained-coin
singleton calculation to arbitrary side information. -/
theorem coinTrueFiberCount_withSide_trueFiber
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  unfold coinTrueFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- If a retained side-channel fiber has no false-side output matching the
selected true-side output, then the corresponding false-side pair fiber is
empty. -/
theorem coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) = 0 := by
  unfold coinFalseFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r false c, side c) = (r true c₀, side c₀)) (fun c h => by
      have hside : side c = side c₀ := congrArg Prod.snd h
      have hout : r false c = r true c₀ := congrArg Prod.fst h
      exact hsep c hside hout)

/-- Exact forward defect for an arbitrary retained side-channel output fiber.
Keeping enough side information to isolate a true-side output from all
false-side outputs in that side fiber revives the source-product obstruction,
scaled by the true-side size of the selected side-channel fiber. -/
theorem countIndependentWithinForwardGap_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, side c)) (r true c₀, side c₀)
  have htrue := coinTrueFiberCount_withSide_trueFiber r side c₀
  have hfalse := coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    r side c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of an output that retains a side channel forces
the tolerance to dominate the side-fiber source-product defect. -/
theorem sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r true c = r true c₀ ∧ side c = side c₀) ≤ τ := by
  have hgap := countIndependentWithinForwardGap_sideRetained_trueFiber
    C E r side c₀ hsep
  have hcert :
      countIndependentWithinForwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) =
            (r true c₀, side c₀)) ≤ τ :=
    (happrox (r true c₀, side c₀)).1
  rw [hgap] at hcert
  exact hcert

/-- Source and side-fiber lower-bound form of the retained-side-channel
obstruction. -/
theorem sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hside)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained side-channel outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_product_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r true c = r true c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox)

/-- Source/side lower-bound strict-tolerance blocker for retained side-channel
outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_sourceSideLowerBounds_mul_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox)

/-- For a retained side channel, the false-side fiber at a fixed side value is
the false output/side equality class. -/
theorem coinFalseFiberCount_withSide_falseFiber
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  unfold coinFalseFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- If a retained side-channel fiber has no true-side output matching the
selected false-side output, then the corresponding true-side pair fiber is
empty. -/
theorem coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) = 0 := by
  unfold coinTrueFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r true c, side c) = (r false c₀, side c₀)) (fun c h => by
      have hside : side c = side c₀ := congrArg Prod.snd h
      have hout : r true c = r false c₀ := congrArg Prod.fst h
      exact hsep c hside hout)

/-- Exact backward defect for an arbitrary retained side-channel false-side
output fiber.  This is the symmetric companion to
`countIndependentWithinForwardGap_sideRetained_trueFiber`. -/
theorem countIndependentWithinBackwardGap_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, side c)) (r false c₀, side c₀)
  have hfalse := coinFalseFiberCount_withSide_falseFiber r side c₀
  have htrue := coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    r side c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of an output that retains a side channel forces
the tolerance to dominate a false-side side-fiber source-product defect. -/
theorem sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r false c = r false c₀ ∧ side c = side c₀) ≤ τ := by
  have hgap := countIndependentWithinBackwardGap_sideRetained_falseFiber
    C E r side c₀ hsep
  have hcert :
      countIndependentWithinBackwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) =
            (r false c₀, side c₀)) ≤ τ :=
    (happrox (r false c₀, side c₀)).2
  rw [hgap] at hcert
  exact hcert

/-- Source and side-fiber lower-bound form of the false-side retained
side-channel obstruction. -/
theorem sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hside)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained side-channel false-side outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_product_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r false c = r false c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox)

/-- Source/side lower-bound strict-tolerance blocker for retained side-channel
false-side outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_sourceSideLowerBounds_mul_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox)

/-- A postprocessed retained side-channel output has balanced finite-coin
fibers exactly when every observed postprocessed value has the same number of
true-side and false-side coin witnesses.  This is the exact cancellation shape
left after hashing or otherwise observing the retained output/side pair. -/
theorem finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  rfl

/-- Source lower-bound postprocessed-side quantization: below one
lower-bounded source/coin block, approximate independence of any deterministic
postprocessing of the retained-side output is equivalent to exact true/false
balance in every observed postprocessed fiber. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => post (r b c, side c)) htrue hfalse hlt
    _ ↔ ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
            r side post

/-- Exact source-count specialization of postprocessed-side quantization. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_observedFiber_count_eq
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
      C E r side post le_rfl le_rfl hlt

/-- Quantitative postprocessed-side obligation: approximate output
independence forces every observed postprocessed fiber's true-minus-false and
false-minus-true residual imbalance to fit inside the tolerance budget.  This
does not require an isolated observed value; any imperfect cancellation after
hashing still contributes a source/coin-scaled defect. -/
theorem sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) := by
  constructor
  · intro z
    have h :=
      sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
        C E (fun b c => post (r b c, side c)) z τ loTrue loFalse
        htrue hfalse happrox
    simpa [coinTrueFiberCount, coinFalseFiberCount] using h
  · intro z
    have h :=
      sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
        C E (fun b c => post (r b c, side c)) z τ loTrue loFalse
        htrue hfalse happrox
    simpa [coinTrueFiberCount, coinFalseFiberCount] using h

/-- Strict-tolerance blocker for a positive true-minus-false observed-fiber
imbalance after deterministic postprocessing of the retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_trueMinusFalse_sourceLowerBounds_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  have hbounds :=
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (hbounds.1 z)

/-- Strict-tolerance blocker for a positive false-minus-true observed-fiber
imbalance after deterministic postprocessing of the retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_falseMinusTrue_sourceLowerBounds_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  have hbounds :=
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (hbounds.2 z)

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side output erases every decidable downstream property:
the property has exactly the same true-side and false-side coin counts.  This
is the predicate-level form between observed-fiber balance and Boolean decoder
half-accuracy. -/
theorem postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E (fun b c => post (r b c, side c)) htrue hfalse hlt).1 happrox
  simpa using
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      (fun b c => post (r b c, side c)) P hbal

/-- Strict downstream-predicate blocker for a postprocessed retained-side
output: below one lower-bounded source/coin block, any predicate with a
true-side count advantage refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) <
        finiteEventCount Coin (fun c => P (post (r true c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox)

/-- Strict downstream-predicate blocker for a postprocessed retained-side
output: below one lower-bounded source/coin block, any predicate with a
false-side count advantage refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_falseCount_gt_trueCount_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) <
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox).symm

/-- Strict downstream-predicate separation blocker for a postprocessed
retained-side output: below one lower-bounded source/coin block, a predicate
that contains every true-side observation and no false-side observation refutes
approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (htruePred : ∀ c : Coin, P (post (r true c, side c)))
    (hfalsePred : ∀ c : Coin, ¬ P (post (r false c, side c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  have hfalseZero :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) = 0 := by
    exact finiteEventCount_zero_of_forall_not
      (fun c => P (post (r false c, side c)))
      (fun c hc => hfalsePred c hc)
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  have htruePos :
      0 < finiteEventCount Coin (fun c => P (post (r true c, side c))) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨c₀, htruePred c₀⟩⟩
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt (by simpa [hfalseZero] using htruePos)

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side output forces every downstream Boolean decoder to
be exactly half-accurate in aggregate across the two source sides.  A decoder
cannot recover source information after hashing unless the observed fibers
already violate the below-threshold independence certificate. -/
theorem postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E (fun b c => post (r b c, side c)) htrue hfalse hlt).1 happrox
  simpa using
    finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
      (fun b c => post (r b c, side c)) decode hbal

/-- Strict downstream-decoder blocker for a postprocessed retained-side output:
below one lower-bounded source/coin block, any Boolean decoder with
better-than-half aggregate accuracy refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_gt_card_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      Fintype.card Coin <
        finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
          finiteEventCount Coin
            (fun c => decode (post (r false c, side c)) = false)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt happrox)

/-- Uniform downstream-decoder recovery is incompatible with below-threshold
approximate independence of a postprocessed retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => decode z = true) htrue hfalse hlt
      hdecodeTrue
      (fun c h => by
        have hfalseDecode : decode (post (r false c, side c)) = false :=
          hdecodeFalse c
        rw [h] at hfalseDecode
        cases hfalseDecode)

/-- Disjoint true-side and false-side observed supports after retained-side
postprocessing are incompatible with below-threshold approximate output
independence.  Hashing or otherwise postprocessing the retained pair must
create source-side support collisions, not merely hide the original syntax. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  classical
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post
      (fun z => ∃ cTrue : Coin, post (r true cTrue, side cTrue) = z)
      htrue hfalse hlt
      (fun c => ⟨c, rfl⟩)
      (fun cFalse h => by
        rcases h with ⟨cTrue, hEq⟩
        exact hsep cTrue cFalse hEq)

/-- Positive collision obligation for a postprocessed retained-side output:
below one lower-bounded source/coin block, approximate output independence
forces at least one true-side observed value and one false-side observed value
to collide after postprocessing.  A deterministic hash repair must therefore
create real observed support overlap, not merely conceal the retained pair. -/
theorem exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  by_contra hnone
  have hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse) := by
    intro cTrue cFalse hEq
    exact hnone ⟨cTrue, cFalse, hEq⟩
  exact
    (not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hsep) happrox

/-- Pointwise true-side collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, every true-side coin's
observed postprocessed value must also be observed on the false side. -/
theorem exists_false_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ)
    (cTrue : Coin) :
    ∃ cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  have hcount :=
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => z = post (r true cTrue, side cTrue))
      htrue hfalse hlt happrox
  have htruePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r true c, side c) = post (r true cTrue, side cTrue)) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨cTrue, rfl⟩⟩
  have hfalsePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r false c, side c) = post (r true cTrue, side cTrue)) := by
    simpa [hcount] using htruePos
  unfold finiteEventCount at hfalsePos
  rcases Fintype.card_pos_iff.mp hfalsePos with ⟨cFalse⟩
  exact ⟨cFalse.1, cFalse.2.symm⟩

/-- Pointwise false-side collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, every false-side coin's
observed postprocessed value must also be observed on the true side. -/
theorem exists_true_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ)
    (cFalse : Coin) :
    ∃ cTrue : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  have hcount :=
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => z = post (r false cFalse, side cFalse))
      htrue hfalse hlt happrox
  have hfalsePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r false c, side c) = post (r false cFalse, side cFalse)) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨cFalse, rfl⟩⟩
  have htruePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r true c, side c) = post (r false cFalse, side cFalse)) := by
    simpa [hcount] using hfalsePos
  unfold finiteEventCount at htruePos
  rcases Fintype.card_pos_iff.mp htruePos with ⟨cTrue⟩
  exact ⟨cTrue.1, cTrue.2⟩

/-- Symmetric pointwise collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, the true-side and false-side
observed supports coincide pointwise.  A repair must overlap every observed
coin value on both source sides, not merely produce a single collision. -/
theorem postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) := by
  exact
    ⟨fun cTrue =>
        exists_false_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
          C E r side post htrue hfalse hlt happrox cTrue,
      fun cFalse =>
        exists_true_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
          C E r side post htrue hfalse hlt happrox cFalse⟩

/-- A three-coin retained-side postprocessing audit instance.  Both source
sides observe the same two values, but with multiplicities `2,1` versus `1,2`.
This is the minimal finite pattern showing that pointwise support overlap is
strictly weaker than the preserving coin-equivalence obligation. -/
def postprocessedSidePointwiseCollisionSkewRecoding (b : Bool) (c : Fin 3) :
    Bool :=
  if b = true then decide (c.val < 2) else decide (c.val = 0)

/-- In the skew three-coin audit instance, every true-side observed value has a
false-side witness and every false-side observed value has a true-side witness.
Thus pointwise collisions/support overlap alone can hold. -/
theorem postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions :
    (∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) := by
  constructor
  · intro cTrue
    fin_cases cTrue
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨1, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
  · intro cFalse
    fin_cases cFalse
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨2, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨2, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩

/-- In the skew three-coin audit instance, no bijective coin matching can
preserve the postprocessed observation.  Two true-side coins with observed
value `true` would both have to map to the unique false-side coin with that
same observed value. -/
theorem postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving :
    ¬ ∃ e : Fin 3 ≃ Fin 3,
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (e c) := by
  rintro ⟨e, hpres⟩
  have hfalse_true_eq_zero :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding false c = true →
          c = 0 := by
    intro c hc
    fin_cases c <;>
      simp [postprocessedSidePointwiseCollisionSkewRecoding] at hc ⊢
  have he0 : e 0 = 0 := by
    apply hfalse_true_eq_zero
    simpa [postprocessedSidePointwiseCollisionSkewRecoding] using
      (hpres 0).symm
  have he1 : e 1 = 0 := by
    apply hfalse_true_eq_zero
    simpa [postprocessedSidePointwiseCollisionSkewRecoding] using
      (hpres 1).symm
  have h01 : (0 : Fin 3) = 1 := by
    apply e.injective
    rw [he0, he1]
  norm_num at h01

/-- Pointwise true/false support overlap does not imply the postprocessed-side
coin-matching obligation.  This blocks the repair route that tries to replace
the preserving coin equivalence with mere two-sided support collisions. -/
theorem postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) := by
  refine
    ⟨postprocessedSidePointwiseCollisionSkewRecoding,
      (fun _c => ()), (fun x : Bool × Unit => x.1), ?_⟩
  exact
    ⟨postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions,
      postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving⟩

/-- A one-sided true-to-false coin map preserving postprocessed observations
promotes to the required preserving coin equivalence as soon as it is
injective.  Thus the missing datum in a witness-choice repair is not the
choice function itself, but its finite injectivity/bijectivity. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hinj : Function.Injective f) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  classical
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  let e : Coin ≃ Coin := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro c
  change post (r true c, side c) = post (r false (f c), side (f c))
  exact hpres c

/-- Contrapositive form of the one-sided-map audit: whenever no preserving
postprocessed-side coin equivalence exists, every one-sided preserving
true-to-false coin map must collapse two coin choices. -/
theorem not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ Function.Injective f := by
  intro hinj
  exact hno
    (exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
      r side post f hpres hinj)

/-- An injective one-sided witness map is not a weaker repair target: for a
finite coin type it is equivalent to the full preserving postprocessed-side
coin equivalence.  The forward direction promotes injectivity to bijectivity;
the reverse direction forgets the equivalence to its underlying function. -/
theorem exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  constructor
  · rintro ⟨f, hpres, hinj⟩
    exact
      exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
        r side post f hpres hinj
  · rintro ⟨e, hpres⟩
    refine ⟨fun c => e c, ?_, e.injective⟩
    exact hpres

/-- A concrete one-sided witness map for the skew three-coin instance.  It
sends both true-side coins with observed value `true` to the unique false-side
coin with observed value `true`, and sends the remaining true-side coin to a
false-side coin with observed value `false`. -/
def postprocessedSidePointwiseCollisionSkewTrueToFalseMap (c : Fin 3) : Fin 3 :=
  if postprocessedSidePointwiseCollisionSkewRecoding true c = true then 0 else 1

/-- The concrete skew witness map preserves the postprocessed observation. -/
theorem postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving :
    ∀ c : Fin 3,
      postprocessedSidePointwiseCollisionSkewRecoding true c =
        postprocessedSidePointwiseCollisionSkewRecoding false
          (postprocessedSidePointwiseCollisionSkewTrueToFalseMap c) := by
  intro c
  fin_cases c <;>
    simp [postprocessedSidePointwiseCollisionSkewRecoding,
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap]

/-- The concrete skew witness map is necessarily non-injective: it collapses
the two true-side coins whose postprocessed observation is `true`. -/
theorem postprocessedSidePointwiseCollisionSkew_trueToFalseMap_not_injective :
    ¬ Function.Injective postprocessedSidePointwiseCollisionSkewTrueToFalseMap := by
  intro hinj
  have hsame :
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap (0 : Fin 3) =
        postprocessedSidePointwiseCollisionSkewTrueToFalseMap 1 := by
    simp [postprocessedSidePointwiseCollisionSkewRecoding,
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap]
  have h01 : (0 : Fin 3) = 1 := hinj hsame
  norm_num at h01

/-- In the skew three-coin instance, every one-sided true-to-false map that
preserves the postprocessed observation is non-injective.  This blocks the
repair route that tries to choose a false-side witness for each true-side coin
without proving the choice is an injective/bijective matching. -/
theorem postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective
    (f : Fin 3 → Fin 3)
    (hpres :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (f c)) :
    ¬ Function.Injective f := by
  have hpres' :
      ∀ c : Fin 3,
        (fun x : Bool × Unit => x.1)
            (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) =
          (fun x : Bool × Unit => x.1)
            (postprocessedSidePointwiseCollisionSkewRecoding false (f c), ()) := by
    intro c
    exact hpres c
  have hno :
      ¬ ∃ e : Fin 3 ≃ Fin 3,
        ∀ c : Fin 3,
          (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) =
            (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding false (e c), ()) := by
    simpa using postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      postprocessedSidePointwiseCollisionSkewRecoding (fun _c => ())
      (fun x : Bool × Unit => x.1) f hpres' hno

/-- A one-sided witness-choice repair is still strictly weaker than the
postprocessed-side preserving coin equivalence: the skew instance has
one-sided preserving maps, but every such map is non-injective and hence cannot
be promoted to a bijective matching. -/
theorem postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) := by
  refine
    ⟨postprocessedSidePointwiseCollisionSkewRecoding,
      (fun _c => ()), (fun x : Bool × Unit => x.1), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨postprocessedSidePointwiseCollisionSkewTrueToFalseMap,
        postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving⟩
  · intro f hpres
    exact postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective f hpres
  · exact postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving

/-- Exact fiber matching for postprocessed retained-side observations: if the
true-side and false-side observed fibers have equal finite counts at every
postprocessed value, then there is a global equivalence of coin choices that
preserves the postprocessed observation.  This records the multiplicity-level
obligation behind pointwise support overlap. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (hcount :
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  classical
  let trueObs : Coin → β := fun c => post (r true c, side c)
  let falseObs : Coin → β := fun c => post (r false c, side c)
  let fiberEquiv :
      ∀ z : β, {c : Coin // trueObs c = z} ≃ {c : Coin // falseObs c = z} :=
    fun z =>
      Fintype.equivOfCardEq (by
        simpa [trueObs, falseObs, finiteEventCount] using hcount z)
  let e : Coin ≃ Coin :=
    (Equiv.sigmaFiberEquiv trueObs).symm.trans
      ((Equiv.sigmaCongrRight fiberEquiv).trans
        (Equiv.sigmaFiberEquiv falseObs))
  refine ⟨e, ?_⟩
  intro c
  let x : {cFalse : Coin // falseObs cFalse = trueObs c} :=
    fiberEquiv (trueObs c) ⟨c, rfl⟩
  have hx : falseObs x.1 = trueObs c := x.2
  change trueObs c = falseObs (e c)
  rw [show e c = x.1 from rfl]
  exact hx.symm

/-- Global matching obligation for a postprocessed retained-side output:
below one lower-bounded source/coin block, approximate output independence
forces a bijective matching of coin choices that preserves every
postprocessed observation.  A deterministic postprocessing repair must
therefore preserve exact observed multiplicities, not just create support
overlap. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post
      ((countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
        C E r side post htrue hfalse hlt).mp happrox)

/-- Contrapositive matching blocker for postprocessed retained-side outputs:
if there is no bijection of coin choices preserving the postprocessed
observation from the true side to the false side, then below-threshold
approximate output independence is impossible. -/
theorem not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact hno
    (exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox)

/-- Any bijective true/false coin matching that preserves postprocessed
observations forces exact equality of every observed postprocessed fiber count.
This is the converse audit for proposed matching repairs: a bijection cannot
repair even one multiplicity mismatch. -/
theorem postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  classical
  intro z
  let trueObs : Coin → β := fun c => post (r true c, side c)
  let falseObs : Coin → β := fun c => post (r false c, side c)
  let fiberEquiv :
      {c : Coin // trueObs c = z} ≃ {c : Coin // falseObs c = z} :=
    { toFun := fun c => by
        refine ⟨e c.1, ?_⟩
        change post (r false (e c.1), side (e c.1)) = z
        rw [← hpres c.1]
        simpa [trueObs] using c.2
      invFun := fun c => by
        refine ⟨e.symm c.1, ?_⟩
        change post (r true (e.symm c.1), side (e.symm c.1)) = z
        rw [hpres (e.symm c.1)]
        simpa [falseObs] using c.2
      left_inv := by
        intro c
        ext
        simp
      right_inv := by
        intro c
        ext
        simp }
  simpa [finiteEventCount, trueObs, falseObs] using Fintype.card_congr fiberEquiv

/-- Injective one-sided witness maps are exactly the observed-fiber
multiplicity-balance obligation.  This removes the apparent intermediate repair
target: with finite coins, proving an injective one-sided choice of false-side
witnesses is the same count-theoretic burden as proving a preserving
postprocessed-side coin equivalence. -/
theorem exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · intro h
    rcases
      (exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
        r side post).1 h with ⟨e, hpres⟩
    exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving r side post e hpres
  · intro hcount
    rcases exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post hcount with ⟨e, hpres⟩
    exact
      (exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
        r side post).2 ⟨e, hpres⟩

/-- A single postprocessed observed-fiber multiplicity mismatch rules out every
coin equivalence preserving the postprocessed observation.  This makes the
coin-matching repair obligation checkable by local fiber counts rather than by
searching over all bijections. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres z)

/-- A single postprocessed observed-fiber multiplicity mismatch forces every
one-sided preserving witness map to be non-injective.  This is the general
pigeonhole form of the one-sided-map blocker; it is not tied to the concrete
three-coin skew instance. -/
theorem not_injective_postprocessedSide_coinMap_preserving_of_observedFiber_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      r side post f hpres
      (not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
        r side post z hne)

/-- Concrete multiplicity blocker for postprocessed retained-side outputs:
below one lower-bounded source/coin block, one observed postprocessed fiber
with unequal true-side and false-side coin counts refutes approximate output
independence.  Equivalently, the proposed postprocessing must solve the exact
coin-matching obligation at every observed value. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
        r side post z hne)

/-- In the concrete skew three-coin instance, the observed value `true`
appears twice on the true side. -/
theorem postprocessedSidePointwiseCollisionSkew_true_count_true :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) = 2 := by
  decide

/-- In the concrete skew three-coin instance, the observed value `true`
appears once on the false side. -/
theorem postprocessedSidePointwiseCollisionSkew_false_count_true :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) = 1 := by
  decide

/-- The concrete skew three-coin instance has an observed-fiber multiplicity
mismatch at the value `true`.  This is the exact local obstruction that blocks
below-threshold approximate independence despite pointwise support overlap. -/
theorem postprocessedSidePointwiseCollisionSkew_true_count_ne :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) ≠
      finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) := by
  rw [postprocessedSidePointwiseCollisionSkew_true_count_true,
    postprocessedSidePointwiseCollisionSkew_false_count_true]
  decide

/-- The concrete skew three-coin audit instance fails approximate output
independence below the natural source/coin threshold `3`, even though it has
two-sided pointwise collisions.  This blocks the repair route that replaces
exact multiplicity matching by mere support overlap. -/
theorem postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
    {τ : Nat} (htol : τ < 3) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  have htrue : 1 ≤ finiteEventCount Bool (fun ω => True ∧ ω = true) := by
    decide
  have hfalse : 1 ≤ finiteEventCount Bool (fun ω => True ∧ ¬ (ω = true)) := by
    decide
  have hlt : τ < 1 * 1 * Fintype.card (Fin 3) := by
    simpa using htol
  have hne :
      finiteEventCount (Fin 3)
          (fun c => (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) = true) ≠
        finiteEventCount (Fin 3)
          (fun c => (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding false c, ()) = true) := by
    simpa using postprocessedSidePointwiseCollisionSkew_true_count_ne
  have hblock :=
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
      (Ω := Bool) (Coin := Fin 3) (α := Bool) (Side := Unit) (β := Bool)
      (C := fun _ω => True) (E := fun ω => ω = true)
      postprocessedSidePointwiseCollisionSkewRecoding (fun _c => ())
      (fun x : Bool × Unit => x.1)
      true htrue hfalse hlt hne
  simpa using hblock

/-- In the concrete skew three-coin audit instance, the output fiber `true`
has forward defect exactly `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 3 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `true`
has zero backward defect. -/
theorem postprocessedSidePointwiseCollisionSkew_true_backward_gap_eq_zero :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 0 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `false`
has zero forward defect. -/
theorem postprocessedSidePointwiseCollisionSkew_false_forward_gap_eq_zero :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 0 := by
  decide

/-- In the concrete skew three-coin audit instance, the output fiber `false`
has backward defect exactly `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 3 := by
  decide

/-- The concrete skew three-coin audit instance satisfies approximate output
independence exactly once the tolerance reaches `3`.  This shows the local
lower bound from the multiplicity mismatch is sharp, not merely one-sided. -/
theorem postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le
    {τ : Nat} (hτ : 3 ≤ τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  intro y
  cases y with
  | false =>
      constructor
      · rw [postprocessedSidePointwiseCollisionSkew_false_forward_gap_eq_zero]
        exact Nat.zero_le τ
      · rw [postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three]
        exact hτ
  | true =>
      constructor
      · rw [postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three]
        exact hτ
      · rw [postprocessedSidePointwiseCollisionSkew_true_backward_gap_eq_zero]
        exact Nat.zero_le τ

/-- The skew three-coin postprocessed-side witness has sharp approximate output
threshold `3`: it fails below `3`, and it succeeds from `3` onward. -/
theorem postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_iff_three_le
    {τ : Nat} :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ ↔
      3 ≤ τ := by
  constructor
  · intro h
    by_contra hlt
    exact
      postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
        (Nat.lt_of_not_ge hlt) h
  · intro hτ
    exact
      postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le hτ

/-- Concrete counterexample package for the postprocessed-side repair route:
the skew three-coin instance has pointwise support collisions and even a
one-sided preserving witness map, but still fails approximate independence for
every tolerance below `3`. -/
theorem postprocessedSidePointwiseCollisionSkew_collision_and_oneSidedMap_counterexample_of_lt_three
    {τ : Nat} (htol : τ < 3) :
    ((∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse)) ∧
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true c =
            postprocessedSidePointwiseCollisionSkewRecoding false (f c)) ∧
      ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
        (fun _xr => True)
        (fun xr => xr.1 = true)
        (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  refine ⟨postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions, ?_, ?_⟩
  · exact
      ⟨postprocessedSidePointwiseCollisionSkewTrueToFalseMap,
        postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving⟩
  · exact
      postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
        htol

/-- Any preserving postprocessed-side coin matching erases every downstream
decidable predicate at the level of true/false coin counts.  This packages the
observed-fiber cardinality obligation for repairs that only expose a Boolean
test of the postprocessed observation. -/
theorem postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  have hcount :=
    postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
      r side post).2 hcount
  simpa using
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      (fun b c => post (r b c, side c)) P hbal

/-- A single downstream predicate with unequal true-side and false-side coin
counts rules out every preserving postprocessed-side coin equivalence. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_outputPredicate_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post P e hpres)

/-- Predicate-level coin-matching blocker for postprocessed retained-side
outputs: below one lower-bounded source/coin block, unequal downstream
predicate counts refute approximate output independence by ruling out the
required preserving coin equivalence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_count_ne_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_outputPredicate_count_ne
        r side post P hne)

/-- Any preserving postprocessed-side coin matching makes every downstream
Boolean decoder exactly half-accurate in aggregate across the two source
sides. -/
theorem postprocessedSide_outputDecoder_correctCount_eq_card_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  have hpred :=
    postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post (fun z => decode z = true) e hpres
  rw [hpred]
  exact finiteEventCount_bool_true_add_false
    (fun c => decode (post (r false c, side c)))

/-- A downstream decoder whose aggregate correctness is not exactly half
rules out every preserving postprocessed-side coin equivalence. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_outputDecoder_correctCount_ne_card
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_outputDecoder_correctCount_eq_card_of_coinEquiv_preserving
      r side post decode e hpres)

/-- Decoder-level coin-matching blocker for postprocessed retained-side
outputs: below one lower-bounded source/coin block, any downstream decoder
whose aggregate correctness is not exactly half refutes approximate output
independence by ruling out the required preserving coin equivalence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_ne_card_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_outputDecoder_correctCount_ne_card
        r side post decode hne)

/-- Downstream predicate erasure for a postprocessed retained-side observation
is exactly observed-fiber balance.  Quantifying over all decidable predicates
does not weaken the coin-matching obligation: singleton predicates recover
the original observed fibers. -/
theorem postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∀ P : β → Prop, [DecidablePred P] →
      finiteEventCount Coin (fun c => P (post (r true c, side c))) =
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · intro hpred z
    simpa using hpred (fun y : β => y = z)
  · intro hcount P _hP
    have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
      (finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
        r side post).2 hcount
    simpa using
      finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
        (fun b c => post (r b c, side c)) P hbal

/-- Predicate-only certificates are equivalent to the full preserving
postprocessed-side coin matching.  A repair that claims all downstream
Boolean tests are source-neutral has already accepted the exact observed-fiber
multiplicity obligation needed to build the coin equivalence. -/
theorem exists_postprocessedSide_coinEquiv_preserving_iff_outputPredicate_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  constructor
  · rintro ⟨e, hpres⟩ P _hP
    exact postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post P e hpres
  · intro hpred
    exact
      exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
        r side post
        ((postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
          r side post).1 hpred)

/-- Preserving postprocessed-side coin equivalences are exactly observed-fiber
count balance.  This is the finite distribution form of the coin-matching
obligation, independent of how the repair phrases the matching certificate. -/
theorem exists_postprocessedSide_coinEquiv_preserving_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · rintro ⟨e, hpres⟩
    exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres
  · exact exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side observation is equivalent to downstream predicate
erasure.  This is the predicate-only view of the same observed-fiber matching
boundary. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_outputPredicate_count_eq
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ ∀ z : β,
            finiteEventCount Coin (fun c => post (r true c, side c) = z) =
              finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
            C E r side post htrue hfalse hlt
    _ ↔ ∀ P : β → Prop, [DecidablePred P] →
          finiteEventCount Coin (fun c => P (post (r true c, side c))) =
            finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
          (postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
            r side post).symm

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side observation is equivalent to the existence of a
preserving true/false coin equivalence.  Thus an independence certificate below
this threshold must solve the full finite matching problem. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ ∀ z : β,
            finiteEventCount Coin (fun c => post (r true c, side c) = z) =
              finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
            C E r side post htrue hfalse hlt
    _ ↔ ∃ e : Coin ≃ Coin,
          ∀ c : Coin,
            post (r true c, side c) =
              post (r false (e c), side (e c)) :=
          (exists_postprocessedSide_coinEquiv_preserving_iff_observedFiber_count_eq
            r side post).symm

/-- Exact source-count specialization of the postprocessed-side coin-matching
equivalence. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_coinEquiv_preserving
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
      C E r side post le_rfl le_rfl hlt

/-- If a postprocessed retained side-channel observation separates a selected
true-side value from every false-side value, then the false-side observed fiber
is empty.  This removes the escape of hashing or otherwise observing the
retained pair before certifying decorrelation. -/
theorem coinFalseFiberCount_postprocessedSide_trueFiber_eq_zero_of_forall_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    coinFalseFiberCount (fun b c => post (r b c, side c))
        (post (r true c₀, side c₀)) = 0 := by
  unfold coinFalseFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => post (r false c, side c) = post (r true c₀, side c₀))
    (fun c h => hsep c h)

/-- Exact forward defect for a postprocessed retained side-channel observation
that isolates a selected true-side observed value from all false-side observed
values.  The obstruction is scaled by the true-side size of that observed
fiber, not by syntactic retention of the original pair. -/
theorem countIndependentWithinForwardGap_postprocessedSide_trueFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r true c, side c) = post (r true c₀, side c₀)) := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber
      C E (fun b c => post (r b c, side c)) (post (r true c₀, side c₀))
  have hfalse := coinFalseFiberCount_postprocessedSide_trueFiber_eq_zero_of_forall_ne
    r side post c₀ hsep
  simpa [coinTrueFiberCount, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of a postprocessed retained side-channel output
forces the tolerance to dominate the selected true-side observed-fiber defect. -/
theorem postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_trueFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r true c, side c) = post (r true c₀, side c₀)) ≤ τ := by
  have hgap := countIndependentWithinForwardGap_postprocessedSide_trueFiber
    C E r side post c₀ hsep
  have hcert :
      countIndependentWithinForwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
            post (r true c₀, side c₀)) ≤ τ :=
    (happrox (post (r true c₀, side c₀))).1
  rw [hgap] at hcert
  exact hcert

/-- Source and observed-fiber lower-bound form of the postprocessed retained
side-channel true-side obstruction. -/
theorem sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_trueFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hobs)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ hsep happrox)

/-- Strict-tolerance blocker for a postprocessed retained side-channel
true-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_product_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r true c, side c) = post (r true c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ hsep happrox)

/-- Source/observed-fiber lower-bound strict-tolerance blocker for a
postprocessed retained side-channel true-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_sourceLowerBounds_mul_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox)

/-- If a postprocessed retained side-channel observation separates a selected
false-side value from every true-side value, then the true-side observed fiber
is empty. -/
theorem coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    coinTrueFiberCount (fun b c => post (r b c, side c))
        (post (r false c₀, side c₀)) = 0 := by
  unfold coinTrueFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => post (r true c, side c) = post (r false c₀, side c₀))
    (fun c h => hsep c h)

/-- Exact backward defect for a postprocessed retained side-channel observation
that isolates a selected false-side observed value from all true-side observed
values. -/
theorem countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r false c, side c) = post (r false c₀, side c₀)) := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
      C E (fun b c => post (r b c, side c)) (post (r false c₀, side c₀))
  have htrue := coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    r side post c₀ hsep
  simpa [coinFalseFiberCount, htrue, Nat.mul_assoc] using hgap

/-- Approximate independence of a postprocessed retained side-channel output
forces the tolerance to dominate the selected false-side observed-fiber
defect. -/
theorem postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r false c, side c) = post (r false c₀, side c₀)) ≤ τ := by
  have hgap := countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    C E r side post c₀ hsep
  have hcert :
      countIndependentWithinBackwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
            post (r false c₀, side c₀)) ≤ τ :=
    (happrox (post (r false c₀, side c₀))).2
  rw [hgap] at hcert
  exact hcert

/-- Source and observed-fiber lower-bound form of the postprocessed retained
side-channel false-side obstruction. -/
theorem sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hobs)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox)

/-- Strict-tolerance blocker for a postprocessed retained side-channel
false-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_product_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r false c, side c) = post (r false c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox)

/-- Source/observed-fiber lower-bound strict-tolerance blocker for a
postprocessed retained side-channel false-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_sourceLowerBounds_mul_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox)

/-- Finite-coin output-variable obligation for a randomized recoding whose
`y`-fiber uniformly selects the `true` source side for every coin.  Certifying
all output fibers still forces the source-fiber product on the source/coin
product space. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  refine
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2 = y) τ ?_ (happrox y)
  intro xr _hC
  by_cases hE : E xr.1
  · simp [hE, htrue xr.2]
  · simp [hE, hfalse xr.2]

/-- Finite-coin output-variable obligation for a randomized recoding whose
`y`-fiber uniformly selects the `false` source side for every coin. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  refine
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2 = y) τ ?_ (happrox y)
  intro xr _hC
  by_cases hE : E xr.1
  · have hnotF : ¬ r (decide (E xr.1)) xr.2 = y := by
      simpa [hE] using htrue xr.2
    exact iff_of_true hE hnotF
  · have hF : r (decide (E xr.1)) xr.2 = y := by
      simpa [hE] using hfalse xr.2
    exact iff_of_false hE (not_not.mpr hF)

/-- Lower-bound transfer for a finite-coin randomized recoding with a uniform
true-side distinguishing output fiber. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct
      (Ω := Ω × Coin) (fun xr => C xr.1) (fun xr => E xr.1)
      loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrueFiber hfalseFiber happrox)

/-- Lower-bound transfer for a finite-coin randomized recoding with a uniform
false-side distinguishing output fiber. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct
      (Ω := Ω × Coin) (fun xr => C xr.1) (fun xr => E xr.1)
      loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrueFiber hfalseFiber happrox)

/-- Product-defect blocker for a finite-coin randomized recoding with a
uniform true-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Product-defect blocker for a finite-coin randomized recoding with a
uniform false-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Lower-bound contradiction for a finite-coin randomized recoding with a
uniform true-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_lowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Lower-bound contradiction for a finite-coin randomized recoding with a
uniform false-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_lowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Source-count form of the finite-coin true-fiber obligation.  The product
space lower bound factors into the source-side product scaled by the number of
coins on both sides. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  have hprod :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [conditionedSourceFiberProduct, hCE, hCnotE] using hprod

/-- Source-count form of the finite-coin false-fiber obligation. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  have hprod :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [conditionedSourceFiberProduct, hCE, hCnotE] using hprod

/-- Source-count lower-bound transfer for the finite-coin true-fiber case. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  have htrueLift :
      loTrue * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) := by
    have hCE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) htrue) (le_of_eq hCE.symm)
  have hfalseLift :
      loFalse * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) := by
    have hCnotE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ ¬ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) hfalse) (le_of_eq hCnotE.symm)
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ (loTrue * Fintype.card Coin) (loFalse * Fintype.card Coin)
      htrueFiber hfalseFiber htrueLift hfalseLift happrox

/-- Source-count lower-bound transfer for the finite-coin false-fiber case. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  have htrueLift :
      loTrue * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) := by
    have hCE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) htrue) (le_of_eq hCE.symm)
  have hfalseLift :
      loFalse * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) := by
    have hCnotE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ ¬ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) hfalse) (le_of_eq hCnotE.symm)
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ (loTrue * Fintype.card Coin) (loFalse * Fintype.card Coin)
      htrueFiber hfalseFiber htrueLift hfalseLift happrox

/-- Source-count lower-bound contradiction for a finite-coin true-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Source-count lower-bound contradiction for a finite-coin false-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Source-count strict-tolerance blocker for a finite-coin true-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y τ htrue hfalse
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [hCE, hCnotE] using htol

/-- Source-count strict-tolerance blocker for a finite-coin false-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y τ htrue hfalse
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [hCE, hCnotE] using htol

/-- The zero-tolerance approximate repair is already blocked by nondegenerate
coupled conditioning. -/
theorem not_countIndependentWithinTolerance_zero_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  apply not_countIndependentWithinTolerance_of_coupled_product_gt C E F 0 hcouple
  simpa using Nat.mul_pos hpos hneg

/-- The zero-tolerance approximate repair is already blocked by nondegenerate
anti-coupled conditioning. -/
theorem not_countIndependentWithinTolerance_zero_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  apply not_countIndependentWithinTolerance_of_anticoupled_product_gt C E F 0 hanti
  simpa using Nat.mul_pos hpos hneg

/-- A distinguishing arbitrary-codomain deterministic output fiber is blocked
at zero tolerance whenever the conditioned source bit is nondegenerate. -/
theorem not_countIndependentWithinTolerance_zero_of_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) 0 := by
  apply
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y 0 hdistinguish
  simpa using Nat.mul_pos hpos hneg

/-- A nonconstant deterministic output variable is blocked at zero tolerance
whenever the conditioned source bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconst : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
      C E r 0 hnonconst
  simpa using Nat.mul_pos hpos hneg

/-- A finite-coin randomized recoding with a uniform true-side distinguishing
output fiber is blocked at zero tolerance when the lifted conditioned source
bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y 0 htrue hfalse
  simpa using Nat.mul_pos hpos hneg

/-- A finite-coin randomized recoding with a uniform false-side distinguishing
output fiber is blocked at zero tolerance when the lifted conditioned source
bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y 0 htrue hfalse
  simpa using Nat.mul_pos hpos hneg

/-- Source-side nondegeneracy blocks a uniform true-side finite-coin
distinguishing fiber at zero tolerance whenever the coin space is nonempty. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
      C E r y htrue hfalse
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω) hpos)
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω) hneg)

/-- Source-side nondegeneracy blocks a uniform false-side finite-coin
distinguishing fiber at zero tolerance whenever the coin space is nonempty. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
      C E r y htrue hfalse
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω) hpos)
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω) hneg)

end Mettapedia.Computability.PNP
