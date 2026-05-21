import Mettapedia.Computability.PNP.FiniteSwitchingAdmissibility
import Mathlib

open scoped BigOperators

/-!
# P vs NP crux: conditioning can destroy a perfectly uniform label map

This file records the simplest exact countermodel to any naive transfer from
pre-conditioning label uniformity to post-conditioning label uniformity.  Start
with the canonical uniform label map on `Fin d × Label`, namely projection to the
second coordinate.  If one conditions on a single label fiber, the conditional
distribution collapses to a point mass on that label.

So even perfect pre-conditioning uniformity says nothing by itself about the
distribution after conditioning on an event such as uniqueness.
-/

namespace Mettapedia.Computability.PNP

section

variable {Label : Type*} [Fintype Label] [DecidableEq Label]

/-- The fiber over `b` for the canonical uniform label map `(i,ℓ) ↦ ℓ`. -/
def canonicalLabelFiber (d : Nat) (b : Label) := { p : Fin d × Label // p.2 = b }

noncomputable instance canonicalLabelFiberFintype (d : Nat) (b : Label) :
    Fintype (canonicalLabelFiber d b) := by
  classical
  dsimp [canonicalLabelFiber]
  infer_instance

noncomputable def canonicalLabelFiberEquiv (d : Nat) (b : Label) :
    canonicalLabelFiber d b ≃ Fin d where
  toFun s := s.1.1
  invFun i := ⟨(i, b), rfl⟩
  left_inv s := by
    cases s with
    | mk p hp =>
        cases p with
        | mk i ℓ =>
            simp at hp
            simp [hp]
  right_inv i := by
    simp

theorem card_canonicalLabelFiber (d : Nat) (b : Label) :
    Fintype.card (canonicalLabelFiber d b) = d := by
  simpa using (Fintype.card_congr (canonicalLabelFiberEquiv d b))

theorem conditioned_target_indicator_average_eq_one
    {d : Nat} (hd : 0 < d) (b : Label) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 1 := by
  have hcard : Fintype.card (canonicalLabelFiber d b) = d := card_canonicalLabelFiber d b
  have hd0 : (Fintype.card (canonicalLabelFiber d b) : ℝ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast Nat.ne_of_gt hd
  have hsum :
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0)
        = Fintype.card (canonicalLabelFiber d b) := by
    calc
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0)
        = ∑ _s : canonicalLabelFiber d b, (1 : ℝ) := by
            refine Fintype.sum_congr
              (fun s : canonicalLabelFiber d b => (if s.1.2 = b then (1 : ℝ) else 0))
              (fun _s : canonicalLabelFiber d b => (1 : ℝ)) ?_
            intro s
            simp [s.2]
      _ = Fintype.card (canonicalLabelFiber d b) := by simp
  rw [hsum, hcard]
  field_simp [hd0]

theorem conditioned_other_indicator_average_eq_zero
    {d : Nat} {b c : Label} (hbc : c ≠ b) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 0 := by
  have hcard : Fintype.card (canonicalLabelFiber d b) = d := card_canonicalLabelFiber d b
  have hsum :
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0) = (0 : ℝ) := by
    calc
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0)
        = ∑ _s : canonicalLabelFiber d b, (0 : ℝ) := by
            refine Fintype.sum_congr
              (fun s : canonicalLabelFiber d b => (if s.1.2 = c then (1 : ℝ) else 0))
              (fun _s : canonicalLabelFiber d b => (0 : ℝ)) ?_
            intro s
            have hs : s.1.2 ≠ c := by
              intro h
              apply hbc
              calc
                c = s.1.2 := h.symm
                _ = b := s.2
            simp [hs]
      _ = (0 : ℝ) := by simp
  rw [hsum, hcard]
  simp

end

/-!
## Conditioning can also destroy independence

The previous section shows collapse of a uniform label map after conditioning on
one label fiber.  The Boolean countermodel below records the sharper v11-style
audit point: even exact unconditioned independence between two coordinates need
not survive conditioning on a promise event that couples them.
-/

/-- Uniform-count independence: `E` and `F` satisfy the cross-multiplied
finite-probability independence equation. -/
def CountIndependent {Ω : Type*} [Fintype Ω]
    (E F : Ω → Prop) [DecidablePred E] [DecidablePred F]
    [DecidablePred (fun ω => E ω ∧ F ω)] : Prop :=
  Fintype.card Ω * finiteEventCount Ω (fun ω => E ω ∧ F ω) =
    finiteEventCount Ω E * finiteEventCount Ω F

/-- Conditional uniform-count independence inside a conditioning event `C`.
The equation is cross-multiplied to avoid division and therefore remains a pure
finite counting obligation. -/
def CountIndependentWithin {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C]
    [DecidablePred (fun ω => C ω ∧ E ω)]
    [DecidablePred (fun ω => C ω ∧ F ω)]
    [DecidablePred (fun ω => C ω ∧ E ω ∧ F ω)] : Prop :=
  finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω)

private noncomputable def eventSplitEquiv {Ω : Type*}
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

private theorem finiteEventCount_split_by {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    finiteEventCount Ω C =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  simpa [finiteEventCount, Fintype.card_sum] using
    Fintype.card_congr (eventSplitEquiv C E)

private theorem finiteEventCount_congr_local {Ω : Type*} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  exact le_antisymm
    (finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE))
    (finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF))

/-- Under deterministic coupling inside `C`, conditional independence is
equivalent to a degenerate conditional event: either `E` never occurs inside
`C`, or `E` always occurs inside `C`.  This is the exact finite-count boundary
behind the diagonal Boolean obstruction. -/
theorem countIndependentWithin_coupled_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  constructor
  · intro hind
    have hind' :
        finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind
    by_cases hce : finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0
    · exact Or.inl hce
    · right
      have hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω) :=
        Nat.pos_of_ne_zero hce
      have hcancel :
          finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) :=
        Nat.mul_right_cancel hpos hind'
      have hsplit := finiteEventCount_split_by (Ω := Ω) C E
      omega
  · intro hdeg
    rcases hdeg with hce | hneg
    · simp [CountIndependentWithin, hCEF, hCF, hce]
    · have hsplit := finiteEventCount_split_by (Ω := Ω) C E
      have hcancel :
          finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
        omega
      simp [CountIndependentWithin, hCEF, hCF, hcancel]

/-- If, inside a conditioning event `C`, the events `E` and `F` are pointwise
equivalent but `E` is nonconstant on `C`, then `E` and `F` cannot be
conditionally independent under uniform finite counting.  This is the abstract
form of the diagonal Boolean obstruction: deterministic coupling plus both
truth values kills conditional independence. -/
theorem not_countIndependentWithin_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  have hcancel :
      finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    have hind' :
        finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind
    exact Nat.mul_right_cancel hpos hind'
  have hsplit := finiteEventCount_split_by (Ω := Ω) C E
  rw [hcancel] at hsplit
  have hlt :
      finiteEventCount Ω (fun ω => C ω ∧ E ω) <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    calc
      finiteEventCount Ω (fun ω => C ω ∧ E ω)
          < finiteEventCount Ω (fun ω => C ω ∧ E ω) +
              finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
            Nat.lt_add_of_pos_right hneg
      _ = finiteEventCount Ω (fun ω => C ω ∧ E ω) := hsplit.symm
  exact (Nat.lt_irrefl _ hlt)

/-- Under deterministic anti-coupling inside `C`, conditional independence is
equivalent to a degenerate conditional event: either `E` never occurs inside
`C`, or `E` always occurs inside `C`.  This is the complement-coded version of
the diagonal Boolean obstruction. -/
theorem countIndependentWithin_anticoupled_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    apply Nat.eq_zero_of_le_zero
    have hle :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) ≤
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_le_of_imp (Ω := Ω) (fun ω h => by
        exact False.elim ((hanti ω h.1).1 h.2.1 h.2.2))
    simpa [finiteEventCount] using hle
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, fun hE => (hanti ω h.1).1 hE h.2⟩
      · intro h
        refine ⟨h.1, ?_⟩
        by_cases hF : F ω
        · exact hF
        · exact False.elim (h.2 ((hanti ω h.1).2 hF)))
  constructor
  · intro hind
    have hprod :
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind.symm
    exact Nat.mul_eq_zero.mp hprod
  · intro hdeg
    rcases hdeg with hce | hneg
    · simp [CountIndependentWithin, hCEF, hCF, hce]
    · simp [CountIndependentWithin, hCEF, hCF, hneg]

/-- If, inside a conditioning event `C`, the events `E` and `F` are pointwise
opposite and `E` is nonconstant on `C`, then `E` and `F` cannot be conditionally
independent under uniform finite counting. -/
theorem not_countIndependentWithin_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  rcases (countIndependentWithin_anticoupled_iff_degenerate_on_condition
      C E F hanti).mp hind with hce | hne
  · exact (Nat.ne_of_gt hpos) hce
  · exact (Nat.ne_of_gt hneg) hne

/-- If the right event is false throughout the conditioning event, it is
conditionally independent of every left event in the cross-multiplied finite
counting sense. -/
theorem countIndependentWithin_of_right_false_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hfalse : ∀ ω, C ω → ¬ F ω) :
    CountIndependentWithin (Ω := Ω) C E F := by
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) = 0 := by
    have hcongr :
        finiteEventCount Ω (fun ω => C ω ∧ F ω) =
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_congr_local (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact False.elim (hfalse ω h.1 h.2)
        · intro h
          exact False.elim h)
    simpa [finiteEventCount] using hcongr
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    have hcongr :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_congr_local (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact False.elim (hfalse ω h.1 h.2.2)
        · intro h
          exact False.elim h)
    simpa [finiteEventCount] using hcongr
  simp [CountIndependentWithin, hCF, hCEF]

/-- If the right event is true throughout the conditioning event, it is
conditionally independent of every left event in the cross-multiplied finite
counting sense. -/
theorem countIndependentWithin_of_right_true_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (htrue : ∀ ω, C ω → F ω) :
    CountIndependentWithin (Ω := Ω) C E F := by
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω C := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact h.1
      · intro hC
        exact ⟨hC, htrue ω hC⟩)
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, htrue ω h.1⟩)
  simp [CountIndependentWithin, hCF, hCEF, Nat.mul_comm]

/-- A nonconstant Boolean recoding of a conditioned bit has the same exact
degeneracy boundary as the copied-bit and complemented-bit cases.  Thus a
repair cannot evade the conditioning obstruction merely by renaming or
recoding the determined conditioned bit. -/
theorem countIndependentWithin_boolRecoding_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  cases ht : r true <;> cases hf : r false
  · exact False.elim (hnonconstant (by simp [ht, hf]))
  · have hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω) := by
      intro ω hC
      have h := hrec ω hC
      by_cases hE : E ω
      · have hnotF : ¬ F ω := by
          intro hF
          have hfalse := h.mp hF
          simp [hE, ht] at hfalse
        exact iff_of_true hE hnotF
      · have hF : F ω := by
          apply h.mpr
          simp [hE, hf]
        exact iff_of_false hE (not_not.mpr hF)
    exact countIndependentWithin_anticoupled_iff_degenerate_on_condition
      C E F hanti
  · have hcouple : ∀ ω, C ω → (E ω ↔ F ω) := by
      intro ω hC
      have h := hrec ω hC
      by_cases hE : E ω
      · have hF : F ω := by
          apply h.mpr
          simp [hE, ht]
        exact iff_of_true hE hF
      · have hnotF : ¬ F ω := by
          intro hF
          have hfalse := h.mp hF
          simp [hE, hf] at hfalse
        exact iff_of_false hE hnotF
    exact countIndependentWithin_coupled_iff_degenerate_on_condition
      C E F hcouple
  · exact False.elim (hnonconstant (by simp [ht, hf]))

/-- A constant Boolean recoding is conditionally independent of the source bit
for the trivial reason that it is constant on the conditioning event. -/
theorem countIndependentWithin_of_boolRecoding_constant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hconstant : r true = r false) :
    CountIndependentWithin (Ω := Ω) C E F := by
  cases ht : r true <;> cases hf : r false
  · apply countIndependentWithin_of_right_false_on_condition C E F
    intro ω hC hF
    have h := (hrec ω hC).mp hF
    by_cases hE : E ω <;> simp [hE, ht, hf] at h
  · simp [ht, hf] at hconstant
  · simp [ht, hf] at hconstant
  · apply countIndependentWithin_of_right_true_on_condition C E F
    intro ω hC
    apply (hrec ω hC).mpr
    by_cases hE : E ω <;> simp [hE, ht, hf]

/-- Exact finite-count classification for deterministic Boolean recodings:
conditional independence holds precisely when the recoding is constant, or the
conditioned source bit is degenerate on the conditioning event. -/
theorem countIndependentWithin_boolRecoding_iff_constant_or_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  constructor
  · intro hind
    by_cases hconstant : r true = r false
    · exact Or.inl hconstant
    · exact Or.inr
        ((countIndependentWithin_boolRecoding_iff_degenerate_on_condition
          C E F r hrec hconstant).mp hind)
  · intro h
    rcases h with hconstant | hdeg
    · exact countIndependentWithin_of_boolRecoding_constant_on_condition
        C E F r hrec hconstant
    · by_cases hconstant : r true = r false
      · exact countIndependentWithin_of_boolRecoding_constant_on_condition
          C E F r hrec hconstant
      · exact
          (countIndependentWithin_boolRecoding_iff_degenerate_on_condition
            C E F r hrec hconstant).mpr hdeg

/-- If the conditioned source bit takes both truth values, a nonconstant
deterministic Boolean recoding cannot be conditionally independent of that
source bit. -/
theorem not_countIndependentWithin_of_boolRecoding_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  rcases (countIndependentWithin_boolRecoding_iff_degenerate_on_condition
      C E F r hrec hnonconstant).mp hind with hce | hne
  · exact (Nat.ne_of_gt hpos) hce
  · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: on a nondegenerate conditioned source bit, every
deterministic Boolean recoding that remains conditionally independent of the
source must be a constant recoding. -/
theorem boolRecoding_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hind : CountIndependentWithin (Ω := Ω) C E F)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  by_contra hnonconstant
  exact not_countIndependentWithin_of_boolRecoding_nonconstant_on_condition
    C E F r hrec hnonconstant hpos hneg hind

/-- On a nondegenerate conditioned source bit, deterministic Boolean recodings
are conditionally independent of the source exactly when they are constant. -/
theorem countIndependentWithin_boolRecoding_iff_constant_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔ r true = r false := by
  constructor
  · intro hind
    exact boolRecoding_constant_of_countIndependentWithin_of_nonconstant_on_condition
      C E F r hrec hind hpos hneg
  · intro hconstant
    exact countIndependentWithin_of_boolRecoding_constant_on_condition
      C E F r hrec hconstant

/-!
The previous Boolean-recoding theorem is not limited to Boolean output labels.
Any deterministic recoding of the same conditioned bit into an arbitrary
decidable codomain has an informative fiber.  If the two source-bit images are
different, the fiber over the `true` image is just the original source bit, so
conditional independence of that fiber has the same degenerate boundary.
-/

/-- Exact finite-count classification for the true-image fiber of an arbitrary
deterministic recoding `Bool → α`.  Conditional independence between the source
bit and that output fiber holds precisely when the recoding collapses the two
source-bit values, or when the source bit is itself degenerate on the
conditioning event. -/
theorem countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hcouple_of_nonconstant
      (hnonconstant : r true ≠ r false) :
      ∀ ω, C ω → (E ω ↔ r (decide (E ω)) = r true) := by
    intro ω _hC
    by_cases hE : E ω
    · simp [hE]
    · have hfalse : r false ≠ r true := fun h => hnonconstant h.symm
      simp [hE, hfalse]
  have hconst_independent
      (hconstant : r true = r false) :
      CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) := by
    refine countIndependentWithin_of_right_true_on_condition
      C E (fun ω => r (decide (E ω)) = r true) ?_
    intro ω _hC
    by_cases hE : E ω <;> simp [hE, hconstant]
  constructor
  · intro hind
    by_cases hconstant : r true = r false
    · exact Or.inl hconstant
    · exact Or.inr
        ((countIndependentWithin_coupled_iff_degenerate_on_condition
          C E (fun ω => r (decide (E ω)) = r true)
          (hcouple_of_nonconstant hconstant)).mp hind)
  · intro h
    rcases h with hconstant | hdeg
    · exact hconst_independent hconstant
    · by_cases hconstant : r true = r false
      · exact hconst_independent hconstant
      · exact
          (countIndependentWithin_coupled_iff_degenerate_on_condition
            C E (fun ω => r (decide (E ω)) = r true)
            (hcouple_of_nonconstant hconstant)).mpr hdeg

/-- A nonconstant arbitrary-codomain deterministic recoding of a nondegenerate
conditioned source bit has an informative output fiber that cannot be
conditionally independent of the source bit. -/
theorem not_countIndependentWithin_of_boolToAnyRecoding_trueFiber_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true) := by
  intro hind
  rcases
      (countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
        C E r).mp hind with hconstant | hdeg
  · exact hnonconstant hconstant
  · rcases hdeg with hce | hne
    · exact (Nat.ne_of_gt hpos) hce
    · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: if the true-image fiber of an arbitrary-codomain
deterministic recoding remains conditionally independent of a nondegenerate
source bit, the recoding must collapse the two source-bit values. -/
theorem boolToAnyRecoding_trueFiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  by_contra hnonconstant
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_trueFiber_nonconstant_on_condition
      C E r hnonconstant hpos hneg hind

/-- On a nondegenerate conditioned source bit, the true-image fiber of an
arbitrary-codomain deterministic recoding is conditionally independent of the
source exactly when the recoding collapses the two source-bit values. -/
theorem countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false := by
  constructor
  · intro hind
    exact
      boolToAnyRecoding_trueFiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
        C E r hind hpos hneg
  · intro hconstant
    exact
      (countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
        C E r).mpr (Or.inl hconstant)

/-- Exact finite-count classification for every output fiber of an arbitrary
deterministic recoding `Bool → α`.  Conditional independence between the source
bit and the fiber `r (decide (E ω)) = y` holds precisely when that fiber does
not distinguish the two source-bit values, or when the source bit is itself
degenerate on the conditioning event. -/
theorem countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hconst_independent
      (hfiber : (r true = y ↔ r false = y)) :
      CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) := by
    by_cases ht : r true = y
    · have hf : r false = y := hfiber.mp ht
      refine countIndependentWithin_of_right_true_on_condition
        C E (fun ω => r (decide (E ω)) = y) ?_
      intro ω _hC
      by_cases hE : E ω <;> simp [hE, ht, hf]
    · have hf : r false ≠ y := fun h => ht (hfiber.mpr h)
      refine countIndependentWithin_of_right_false_on_condition
        C E (fun ω => r (decide (E ω)) = y) ?_
      intro ω _hC hF
      by_cases hE : E ω <;> simp [hE, ht, hf] at hF
  have hcouple_of_true_false
      (ht : r true = y) (hf : r false ≠ y) :
      ∀ ω, C ω → (E ω ↔ r (decide (E ω)) = y) := by
    intro ω _hC
    by_cases hE : E ω
    · simp [hE, ht]
    · simp [hE, hf]
  have hanti_of_false_true
      (ht : r true ≠ y) (hf : r false = y) :
      ∀ ω, C ω → (E ω ↔ ¬ r (decide (E ω)) = y) := by
    intro ω _hC
    by_cases hE : E ω
    · have hnotF : ¬ r (decide (E ω)) = y := by simpa [hE] using ht
      exact iff_of_true hE hnotF
    · have hF : r (decide (E ω)) = y := by simpa [hE] using hf
      exact iff_of_false hE (not_not.mpr hF)
  constructor
  · intro hind
    by_cases hfiber : (r true = y ↔ r false = y)
    · exact Or.inl hfiber
    · by_cases ht : r true = y
      · by_cases hf : r false = y
        · exact False.elim (hfiber (iff_of_true ht hf))
        · exact Or.inr
            ((countIndependentWithin_coupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hcouple_of_true_false ht hf)).mp hind)
      · by_cases hf : r false = y
        · exact Or.inr
            ((countIndependentWithin_anticoupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hanti_of_false_true ht hf)).mp hind)
        · exact False.elim (hfiber (iff_of_false ht hf))
  · intro h
    rcases h with hfiber | hdeg
    · exact hconst_independent hfiber
    · by_cases ht : r true = y
      · by_cases hf : r false = y
        · exact hconst_independent (iff_of_true ht hf)
        · exact
            (countIndependentWithin_coupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hcouple_of_true_false ht hf)).mpr hdeg
      · by_cases hf : r false = y
        · exact
            (countIndependentWithin_anticoupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hanti_of_false_true ht hf)).mpr hdeg
        · exact hconst_independent (iff_of_false ht hf)

/-- If some output fiber of an arbitrary deterministic recoding distinguishes a
nondegenerate conditioned source bit, that fiber cannot be conditionally
independent of the source bit. -/
theorem not_countIndependentWithin_of_boolToAnyRecoding_fiber_distinguishes_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) := by
  intro hind
  rcases
      (countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
        C E r y).mp hind with hfiber | hdeg
  · exact hdistinguish hfiber
  · rcases hdeg with hce | hne
    · exact (Nat.ne_of_gt hpos) hce
    · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: on a nondegenerate conditioned source bit, every
deterministic output fiber that remains conditionally independent must be unable
to distinguish the two source-bit values. -/
theorem boolToAnyRecoding_fiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    (r true = y ↔ r false = y) := by
  by_contra hdistinguish
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_fiber_distinguishes_on_condition
      C E r y hdistinguish hpos hneg hind

/-- On a nondegenerate conditioned source bit, an arbitrary deterministic output
fiber is conditionally independent of the source exactly when that fiber does
not distinguish the two source-bit values. -/
theorem countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) := by
  constructor
  · intro hind
    exact
      boolToAnyRecoding_fiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
        C E r y hind hpos hneg
  · intro hfiber
    exact
      (countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
        C E r y).mpr (Or.inl hfiber)

/-- The smallest finite countermodel for independence-through-conditioning. -/
abbrev ConditioningBoolPair := Bool × Bool

/-- First Boolean coordinate is `true`. -/
def conditioningFirstTrue (ω : ConditioningBoolPair) : Prop := ω.1 = true

instance instDecidablePredConditioningFirstTrue :
    DecidablePred conditioningFirstTrue := by
  intro ω
  unfold conditioningFirstTrue
  infer_instance

/-- Second Boolean coordinate is `true`. -/
def conditioningSecondTrue (ω : ConditioningBoolPair) : Prop := ω.2 = true

instance instDecidablePredConditioningSecondTrue :
    DecidablePred conditioningSecondTrue := by
  intro ω
  unfold conditioningSecondTrue
  infer_instance

/-- Diagonal conditioning event coupling the two coordinates. -/
def conditioningDiagonal (ω : ConditioningBoolPair) : Prop := ω.1 = ω.2

instance instDecidablePredConditioningDiagonal :
    DecidablePred conditioningDiagonal := by
  intro ω
  unfold conditioningDiagonal
  infer_instance

noncomputable def conditioningFirstTrueEquivBool :
    {ω : ConditioningBoolPair // conditioningFirstTrue ω} ≃ Bool where
  toFun ω := ω.1.2
  invFun b := ⟨(true, b), rfl⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningFirstTrue] at h
    subst a
    rfl
  right_inv b := rfl

theorem finiteEventCount_conditioningFirstTrue :
    finiteEventCount ConditioningBoolPair conditioningFirstTrue = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningFirstTrueEquivBool

noncomputable def conditioningSecondTrueEquivBool :
    {ω : ConditioningBoolPair // conditioningSecondTrue ω} ≃ Bool where
  toFun ω := ω.1.1
  invFun a := ⟨(a, true), rfl⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningSecondTrue] at h
    subst b
    rfl
  right_inv a := rfl

theorem finiteEventCount_conditioningSecondTrue :
    finiteEventCount ConditioningBoolPair conditioningSecondTrue = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningSecondTrueEquivBool

noncomputable def conditioningBothTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningFirstTrue ω ∧ conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningFirstTrue, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, ha, hb⟩
    simp [conditioningFirstTrue] at ha
    simp [conditioningSecondTrue] at hb
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningBothTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningFirstTrue ω ∧ conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningBothTrueEquivUnit

noncomputable def conditioningDiagonalEquivBool :
    {ω : ConditioningBoolPair // conditioningDiagonal ω} ≃ Bool where
  toFun ω := ω.1.1
  invFun a := ⟨(a, a), by simp [conditioningDiagonal]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningDiagonal] at h
    subst b
    rfl
  right_inv a := rfl

theorem finiteEventCount_conditioningDiagonal :
    finiteEventCount ConditioningBoolPair conditioningDiagonal = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningDiagonalEquivBool

noncomputable def conditioningDiagonalFirstTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningFirstTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningFirstTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hfirst⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningFirstTrue] at hfirst
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalFirstTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ conditioningFirstTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalFirstTrueEquivUnit

noncomputable def conditioningDiagonalNotFirstTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ ¬ conditioningFirstTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(false, false), by
    simp [conditioningDiagonal, conditioningFirstTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hfirst⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningFirstTrue] at hfirst
    subst b
    cases a
    · rfl
    · contradiction
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalNotFirstTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ ¬ conditioningFirstTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalNotFirstTrueEquivUnit

noncomputable def conditioningDiagonalSecondTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hsecond⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningSecondTrue] at hsecond
    subst b
    subst a
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalSecondTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalSecondTrueEquivUnit

noncomputable def conditioningDiagonalBothTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningFirstTrue ω ∧
        conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningFirstTrue, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, _hdiag, hfirst, hsecond⟩
    simp [conditioningFirstTrue] at hfirst
    simp [conditioningSecondTrue] at hsecond
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalBothTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω =>
        conditioningDiagonal ω ∧ conditioningFirstTrue ω ∧
          conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalBothTrueEquivUnit

/-- Before conditioning, the two Boolean coordinates are independent under
uniform counting. -/
theorem conditioningBoolPair_unconditioned_first_second_independent :
    CountIndependent (Ω := ConditioningBoolPair)
      conditioningFirstTrue conditioningSecondTrue := by
  unfold CountIndependent
  rw [finiteEventCount_conditioningBothTrue,
    finiteEventCount_conditioningFirstTrue,
    finiteEventCount_conditioningSecondTrue]
  norm_num

/-- Conditioning on the diagonal destroys that independence: inside the
conditioned event, the first coordinate determines the second. -/
theorem not_conditioningBoolPair_conditioned_on_diagonal_first_second_independent :
    ¬ CountIndependentWithin (Ω := ConditioningBoolPair)
      conditioningDiagonal conditioningFirstTrue conditioningSecondTrue := by
  exact
    not_countIndependentWithin_of_coupled_nonconstant_on_condition
      (Ω := ConditioningBoolPair)
      conditioningDiagonal conditioningFirstTrue conditioningSecondTrue
      (by
        intro ω hdiag
        rcases ω with ⟨a, b⟩
        simp [conditioningDiagonal, conditioningFirstTrue, conditioningSecondTrue] at hdiag ⊢
        subst b
        rfl)
      (by
        rw [finiteEventCount_conditioningDiagonalFirstTrue]
        norm_num)
      (by
        rw [finiteEventCount_conditioningDiagonalNotFirstTrue]
        norm_num)

end Mettapedia.Computability.PNP
