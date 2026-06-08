/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Billingsley Chapter 3, Section 15: The Integral

This file formalizes Section 15 of Billingsley's "Probability and Measure" (3rd Edition),
constructing the Lebesgue integral of a measurable function with respect to a general
measure.

## Correspondence to mathlib

Billingsley distinguishes:

* `∫ f dμ` for nonnegative `f`, defined as a supremum over simple decompositions
  (equation (15.3)). This is `MeasureTheory.lintegral` in mathlib (ℝ≥0∞-valued).
* `∫ f dμ` for a real-valued `f`, defined as `∫ f⁺ dμ - ∫ f⁻ dμ` (equation (15.6)).
  This is `MeasureTheory.integral` in mathlib for `ℝ`-valued integrable functions
  (Bochner integral).

## Scope

* Definition via simple functions (equation (15.3)).
* `f⁺` and `f⁻` decomposition (equations (15.4), (15.5), (15.6)).
* **Theorem 15.1**: (i) the integral of a simple function equals the finite sum
  `∑ xᵢ μ(Aᵢ)`; (ii) monotonicity; (iii) monotone convergence; (iv) linearity on
  nonnegative functions.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 15][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal Topology

namespace Mettapedia.AutoBooks.Billingsley.Ch03Sec15

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Simple function integrals (Theorem 15.1 (i)) -/

/-- **Theorem 15.1 (i)** (Billingsley): the integral of a nonnegative simple function is
the finite sum of values times measures of the corresponding partition sets. -/
theorem lintegral_simpleFunc (f : MeasureTheory.SimpleFunc Ω ℝ≥0∞) (μ : Measure Ω) :
    ∫⁻ ω, f ω ∂μ = f.lintegral μ := by
  simp [MeasureTheory.SimpleFunc.lintegral_eq_lintegral]

/-! ## Monotonicity (Theorem 15.1 (ii)) -/

/-- **Theorem 15.1 (ii)**: monotonicity of the Lebesgue integral. -/
theorem lintegral_mono_ae {μ : Measure Ω} {f g : Ω → ℝ≥0∞}
    (h : ∀ ω, f ω ≤ g ω) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ :=
  MeasureTheory.lintegral_mono h

/-! ## Monotone convergence (Theorem 15.1 (iii)) -/

/-- **Theorem 15.1 (iii)** / Monotone convergence theorem (Beppo Levi):
if `0 ≤ fₙ ↑ f` then `∫ fₙ dμ ↑ ∫ f dμ`. -/
theorem lintegral_iSup_of_monotone {μ : Measure Ω} (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    ∫⁻ ω, ⨆ n, f n ω ∂μ = ⨆ n, ∫⁻ ω, f n ω ∂μ :=
  MeasureTheory.lintegral_iSup hf hmono

/-! ## Linearity on nonnegative functions (Theorem 15.1 (iv)) -/

/-- **Theorem 15.1 (iv)**: additivity of the Lebesgue integral on measurable nonnegative
functions. -/
theorem lintegral_add_nonneg {μ : Measure Ω} {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) (_hg : Measurable g) :
    ∫⁻ ω, f ω + g ω ∂μ = ∫⁻ ω, f ω ∂μ + ∫⁻ ω, g ω ∂μ :=
  MeasureTheory.lintegral_add_left hf _

/-- **Theorem 15.1 (iv)**: scalar multiples. -/
theorem lintegral_const_mul' {μ : Measure Ω} {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (c : ℝ≥0∞) :
    ∫⁻ ω, c * f ω ∂μ = c * ∫⁻ ω, f ω ∂μ :=
  MeasureTheory.lintegral_const_mul c hf

/-! ## Decomposition of a real-valued measurable function (Billingsley (15.4)–(15.6)) -/

/-- **Billingsley (15.4)**: the positive part of `f`. -/
def posPart (f : Ω → ℝ) : Ω → ℝ := fun ω => max (f ω) 0

/-- **Billingsley (15.5)**: the negative part of `f`. -/
def negPart (f : Ω → ℝ) : Ω → ℝ := fun ω => max (-(f ω)) 0

/-- `f = f⁺ - f⁻`. -/
theorem eq_posPart_sub_negPart (f : Ω → ℝ) (ω : Ω) :
    f ω = posPart f ω - negPart f ω := by
  classical
  by_cases h : 0 ≤ f ω
  · simp [posPart, negPart, h]
  · push_neg at h
    have hneg : 0 ≤ -f ω := by linarith
    simp [posPart, negPart, max_eq_right (le_of_lt h), max_eq_left hneg]

/-- **Billingsley (15.6)**: definition of the integral on general real-valued integrable
functions. In mathlib this is `MeasureTheory.integral`. -/
theorem integral_eq_of_integrable {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = (∫⁻ ω, ENNReal.ofReal (posPart f ω) ∂μ).toReal
                  - (∫⁻ ω, ENNReal.ofReal (negPart f ω) ∂μ).toReal := by
  simpa [posPart, negPart] using
    (MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (μ := μ) hf)

end Mettapedia.AutoBooks.Billingsley.Ch03Sec15
