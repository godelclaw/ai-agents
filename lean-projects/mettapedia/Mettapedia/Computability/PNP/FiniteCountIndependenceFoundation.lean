import Mettapedia.Computability.PNP.ApproximateDecorrelationObstruction

/-!
# P vs NP grassroots: finite-count conditional independence API

The crux modules expose exact finite-count blockers for deterministic and
randomized recodings.  This file starts the grassroots layer underneath those
blocks: small reusable definitions and bridge lemmas around finite conditional
independence itself.

The main design point is to package the two oriented cross-multiplied defects
as one natural-number defect.  Exact conditional independence is then exactly
zero defect, and approximate independence is just a bound on that defect.  This
keeps later route modules from depending on crux-specific theorem names when
all they need is the finite-count interface.
-/

namespace Mettapedia.Computability.PNP

/-- The symmetric finite-count conditional-independence defect of `F` from `E`
inside `C`, written as the maximum of the two oriented cross-product gaps. -/
def countIndependentWithinDefect {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    Nat :=
  max (countIndependentWithinForwardGap (Ω := Ω) C E F)
    (countIndependentWithinBackwardGap (Ω := Ω) C E F)

/-- Bounding the max defect is equivalent to bounding both oriented defects. -/
theorem countIndependentWithinTolerance_iff_defect_le
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ ↔
      countIndependentWithinDefect (Ω := Ω) C E F ≤ τ := by
  simp [CountIndependentWithinTolerance, countIndependentWithinDefect]

/-- Approximate finite-count conditional independence is monotone in the
tolerance. -/
theorem countIndependentWithinTolerance_mono
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    {τ τ' : Nat} (hτ : τ ≤ τ')
    (h : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ' := by
  exact ⟨le_trans h.1 hτ, le_trans h.2 hτ⟩

/-- Zero-tolerance approximate independence is exactly the original
cross-multiplied finite-count independence equation. -/
theorem countIndependentWithinTolerance_zero_iff_countIndependentWithin
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    CountIndependentWithinTolerance (Ω := Ω) C E F 0 ↔
      CountIndependentWithin (Ω := Ω) C E F := by
  constructor
  · intro h
    let lhs :=
      finiteEventCount Ω C *
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω)
    let rhs :=
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ F ω)
    have hf : lhs - rhs ≤ 0 := by
      simpa [lhs, rhs, CountIndependentWithinTolerance,
        countIndependentWithinForwardGap] using h.1
    have hb : rhs - lhs ≤ 0 := by
      simpa [lhs, rhs, CountIndependentWithinTolerance,
        countIndependentWithinBackwardGap] using h.2
    have hlr : lhs ≤ rhs := by omega
    have hrl : rhs ≤ lhs := by omega
    exact le_antisymm hlr hrl
  · intro h
    constructor
    · unfold countIndependentWithinForwardGap
      rw [h]
      simp
    · unfold countIndependentWithinBackwardGap
      rw [h]
      simp

/-- Exact finite-count conditional independence gives approximate independence
at every tolerance. -/
theorem countIndependentWithinTolerance_of_countIndependentWithin
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (h : CountIndependentWithin (Ω := Ω) C E F) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact countIndependentWithinTolerance_mono C E F (Nat.zero_le τ)
    ((countIndependentWithinTolerance_zero_iff_countIndependentWithin C E F).mpr h)

/-- The max defect vanishes exactly when the original finite-count conditional
independence equation holds. -/
theorem countIndependentWithinDefect_eq_zero_iff_countIndependentWithin
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    countIndependentWithinDefect (Ω := Ω) C E F = 0 ↔
      CountIndependentWithin (Ω := Ω) C E F := by
  rw [← countIndependentWithinTolerance_zero_iff_countIndependentWithin C E F]
  simp [countIndependentWithinTolerance_iff_defect_le]

/-- The output-variable certificate specializes to any output fiber. -/
theorem countIndependentWithinToleranceOutput_fiber
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    CountIndependentWithinTolerance (Ω := Ω) C E (fun ω => Y ω = y) τ :=
  h y

/-- The output-variable certificate bounds the forward defect of each fiber. -/
theorem countIndependentWithinToleranceOutput_forwardGap_le
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω) C E (fun ω => Y ω = y) ≤ τ :=
  (h y).1

/-- The output-variable certificate bounds the backward defect of each fiber. -/
theorem countIndependentWithinToleranceOutput_backwardGap_le
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω) C E (fun ω => Y ω = y) ≤ τ :=
  (h y).2

/-- Output-variable approximate independence is monotone in the tolerance. -/
theorem countIndependentWithinToleranceOutput_mono
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) {τ τ' : Nat} (hτ : τ ≤ τ')
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ' := by
  intro y
  exact countIndependentWithinTolerance_mono C E (fun ω => Y ω = y) hτ (h y)

/-- Zero-tolerance output approximate independence is exactly exact finite-count
conditional independence for every output fiber. -/
theorem countIndependentWithinToleranceOutput_zero_iff_countIndependentWithin_fibers
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y 0 ↔
      ∀ y : α, CountIndependentWithin (Ω := Ω) C E (fun ω => Y ω = y) := by
  constructor
  · intro h y
    exact (countIndependentWithinTolerance_zero_iff_countIndependentWithin
      C E (fun ω => Y ω = y)).mp (h y)
  · intro h y
    exact (countIndependentWithinTolerance_zero_iff_countIndependentWithin
      C E (fun ω => Y ω = y)).mpr (h y)

/-- For finite output types, the output defect is the maximum fiber defect over
all output values.  The non-finite-output interface remains the pointwise
predicate `CountIndependentWithinToleranceOutput`; this is the finite summary
used by small-output grassroots routes. -/
def countIndependentWithinOutputDefect {Ω α : Type*} [Fintype Ω] [Fintype α]
    [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) : Nat :=
  (Finset.univ : Finset α).sup
    (fun y => countIndependentWithinDefect (Ω := Ω) C E (fun ω => Y ω = y))

/-- A finite output variable has tolerance `τ` exactly when its maximum fiber
defect is at most `τ`. -/
theorem countIndependentWithinToleranceOutput_iff_outputDefect_le
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ ↔
      countIndependentWithinOutputDefect (Ω := Ω) C E Y ≤ τ := by
  constructor
  · intro h
    unfold countIndependentWithinOutputDefect
    refine Finset.sup_le ?_
    intro y _hy
    exact (countIndependentWithinTolerance_iff_defect_le
      C E (fun ω => Y ω = y) τ).mp (h y)
  · intro h y
    have hy :
        countIndependentWithinDefect (Ω := Ω) C E (fun ω => Y ω = y) ≤
          countIndependentWithinOutputDefect (Ω := Ω) C E Y := by
      unfold countIndependentWithinOutputDefect
      exact Finset.le_sup
        (s := (Finset.univ : Finset α))
        (f := fun y => countIndependentWithinDefect (Ω := Ω) C E (fun ω => Y ω = y))
        (Finset.mem_univ y)
    exact (countIndependentWithinTolerance_iff_defect_le
      C E (fun ω => Y ω = y) τ).mpr (le_trans hy h)

/-- Zero output defect is exact finite-count independence on every output fiber. -/
theorem countIndependentWithinOutputDefect_eq_zero_iff_countIndependentWithin_fibers
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) :
    countIndependentWithinOutputDefect (Ω := Ω) C E Y = 0 ↔
      ∀ y : α, CountIndependentWithin (Ω := Ω) C E (fun ω => Y ω = y) := by
  rw [← countIndependentWithinToleranceOutput_zero_iff_countIndependentWithin_fibers C E Y]
  simp [countIndependentWithinToleranceOutput_iff_outputDefect_le]

end Mettapedia.Computability.PNP
