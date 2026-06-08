import Mettapedia.Computability.PNP.FiniteCountIndependenceFoundation

/-!
# Regression checks for the finite-count conditional-independence API

These wrappers pin the grassroots interface around exact and approximate
finite-count conditional independence.  They deliberately avoid the
recoding-specific crux statements and check only the reusable foundation.
-/

namespace Mettapedia.Computability.PNP.FiniteCountIndependenceFoundationRegression

open Mettapedia.Computability.PNP

theorem tolerance_iff_defect_le_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ ↔
      countIndependentWithinDefect (Ω := Ω) C E F ≤ τ := by
  exact countIndependentWithinTolerance_iff_defect_le C E F τ

theorem tolerance_mono_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    {τ τ' : Nat} (hτ : τ ≤ τ')
    (h : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ' := by
  exact countIndependentWithinTolerance_mono C E F hτ h

theorem zero_tolerance_iff_exact_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    CountIndependentWithinTolerance (Ω := Ω) C E F 0 ↔
      CountIndependentWithin (Ω := Ω) C E F := by
  exact countIndependentWithinTolerance_zero_iff_countIndependentWithin C E F

theorem exact_implies_any_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (h : CountIndependentWithin (Ω := Ω) C E F) :
    CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact countIndependentWithinTolerance_of_countIndependentWithin C E F τ h

theorem defect_zero_iff_exact_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    countIndependentWithinDefect (Ω := Ω) C E F = 0 ↔
      CountIndependentWithin (Ω := Ω) C E F := by
  exact countIndependentWithinDefect_eq_zero_iff_countIndependentWithin C E F

theorem output_fiber_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    CountIndependentWithinTolerance (Ω := Ω) C E (fun ω => Y ω = y) τ := by
  exact countIndependentWithinToleranceOutput_fiber C E Y τ h y

theorem output_forward_gap_le_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω) C E (fun ω => Y ω = y) ≤ τ := by
  exact countIndependentWithinToleranceOutput_forwardGap_le C E Y τ h y

theorem output_backward_gap_le_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat)
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω) C E (fun ω => Y ω = y) ≤ τ := by
  exact countIndependentWithinToleranceOutput_backwardGap_le C E Y τ h y

theorem output_tolerance_mono_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) {τ τ' : Nat} (hτ : τ ≤ τ')
    (h : CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ' := by
  exact countIndependentWithinToleranceOutput_mono C E Y hτ h

theorem output_zero_tolerance_iff_exact_fibers_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y 0 ↔
      ∀ y : α, CountIndependentWithin (Ω := Ω) C E (fun ω => Y ω = y) := by
  exact countIndependentWithinToleranceOutput_zero_iff_countIndependentWithin_fibers C E Y

theorem finite_output_tolerance_iff_max_defect_regression
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat) :
    CountIndependentWithinToleranceOutput (Ω := Ω) C E Y τ ↔
      countIndependentWithinOutputDefect (Ω := Ω) C E Y ≤ τ := by
  exact countIndependentWithinToleranceOutput_iff_outputDefect_le C E Y τ

theorem finite_output_defect_zero_iff_exact_fibers_regression
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) :
    countIndependentWithinOutputDefect (Ω := Ω) C E Y = 0 ↔
      ∀ y : α, CountIndependentWithin (Ω := Ω) C E (fun ω => Y ω = y) := by
  exact countIndependentWithinOutputDefect_eq_zero_iff_countIndependentWithin_fibers C E Y

end Mettapedia.Computability.PNP.FiniteCountIndependenceFoundationRegression
