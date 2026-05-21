import Mettapedia.Computability.PNP.FiniteConsistencyBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# P vs NP background theory: finite weighted agreement mass

This file takes the first step beyond uniform sampling.  Rather than counting
point samples or using only the uniform distribution on a finite input type, we
let one finite probability mass function weight the inputs.

For one predictor `predict` against one target `target`, we define:

* the one-step agreement mass under a `PMF`,
* the mass of a length-`m` sample,
* the total mass of samples on which `predict` agrees with `target`
  everywhere.

The main theorem is exact:

`consistentSampleMass = agreementMass ^ m`.

This is the weighted analogue of the finite counting theorem from
`FiniteConsistencyBound.lean`, and it is the right base lemma for later
distributional or i.i.d. family-level bounds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal
open scoped BigOperators

universe u v

section WeightedAgreement

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]

/-- The total input mass on which `predict` agrees with `target`. -/
noncomputable def agreementMass
    (μ : PMF Input) (target predict : Input → Output) : ℝ≥0∞ :=
  ∑ a : AgreementPoints target predict, μ a.1

/-- Agreement mass as a full input-space indicator sum. -/
theorem agreementMass_eq_sum_indicator
    (μ : PMF Input) (target predict : Input → Output) :
    agreementMass μ target predict =
      ∑ a : Input, if predict a = target a then μ a else 0 := by
  classical
  unfold agreementMass
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset Input))
      (f := fun a : Input => μ a)
      (p := fun a => predict a = target a))

/-- The finite sum of a `PMF` over the full input type is one. -/
theorem pmf_sum_univ_eq_one (μ : PMF Input) :
    (∑ a : Input, μ a) = 1 := by
  classical
  calc
    (∑ a : Input, μ a) = μ.toOuterMeasure (Set.univ : Set Input) := by
      rw [μ.toOuterMeasure_apply_fintype]
      simp
    _ = 1 := by
      simpa using
        (μ.toOuterMeasure_apply_eq_one_iff (s := (Set.univ : Set Input))).2
          (by simp)

/-- If two predictors agree on every positive-mass input, their agreement mass is one. -/
theorem agreementMass_eq_one_of_agrees_on_support
    {μ : PMF Input} {target predict : Input → Output}
    (hagree : ∀ x, μ x ≠ 0 → predict x = target x) :
    agreementMass μ target predict = 1 := by
  classical
  rw [agreementMass_eq_sum_indicator]
  calc
    (∑ a : Input, if predict a = target a then μ a else 0)
        = ∑ a : Input, μ a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hzero : μ a = 0
          · by_cases ha : predict a = target a <;> simp [ha, hzero]
          · simp [hagree a hzero]
    _ = 1 := pmf_sum_univ_eq_one μ

/-- Agreement mass is the `PMF` outer measure of the agreement set. -/
theorem agreementMass_eq_toOuterMeasure_agreementSet
    (μ : PMF Input) (target predict : Input → Output) :
    agreementMass μ target predict =
      μ.toOuterMeasure {x | predict x = target x} := by
  classical
  rw [agreementMass_eq_sum_indicator, μ.toOuterMeasure_apply_fintype]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases ha : predict a = target a <;> simp [Set.indicator, ha]

/-- Any finite region on which `predict` agrees with `target` contributes at
least that region's mass to the total agreement mass. -/
theorem finset_mass_le_agreementMass_of_agrees_on
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → predict x = target x) :
    region.sum (fun x => μ x) ≤ agreementMass μ target predict := by
  classical
  rw [agreementMass_eq_sum_indicator]
  have hregion :
      region.sum (fun x => μ x) =
        region.sum (fun x => if predict x = target x then μ x else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [hagree x hx]
  rw [hregion]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro x hx; exact Finset.mem_univ x)
    (by
      intro x _ _
      by_cases hx : predict x = target x <;> simp [hx])

/-- Any finite region on which `predict` agrees with `target` at every
positive-mass point contributes at least that region's mass to the total
agreement mass.  Zero-mass disagreements are irrelevant for the weighted
bound. -/
theorem finset_mass_le_agreementMass_of_agrees_on_positive
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → μ x ≠ 0 → predict x = target x) :
    region.sum (fun x => μ x) ≤ agreementMass μ target predict := by
  classical
  rw [agreementMass_eq_sum_indicator]
  have hregion :
      region.sum (fun x => μ x) =
        region.sum (fun x => if predict x = target x then μ x else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hzero : μ x = 0
    · by_cases ha : predict x = target x <;> simp [ha, hzero]
    · simp [hagree x hx hzero]
  rw [hregion]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro x hx; exact Finset.mem_univ x)
    (by
      intro x _ _
      by_cases hx : predict x = target x <;> simp [hx])

/-- If a finite region has more mass than the agreement mass, then the region
contains a positive-mass disagreement. -/
theorem exists_pos_mass_disagreement_in_region_of_agreementMass_lt_regionMass
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hmass : agreementMass μ target predict < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧ predict x ≠ target x := by
  classical
  by_contra hnone
  have hagree :
      ∀ x, x ∈ region → μ x ≠ 0 → predict x = target x := by
    intro x hx hμ
    by_contra hneq
    exact hnone ⟨x, hx, hμ, hneq⟩
  exact not_le_of_gt hmass
    (finset_mass_le_agreementMass_of_agrees_on_positive
      (μ := μ) (target := target) (predict := predict) region hagree)

/-- If an external agreement bound is below a finite region's mass, then the
region contains a positive-mass disagreement. -/
theorem exists_pos_mass_disagreement_in_region_of_agreementMass_le_of_lt_regionMass
    {μ : PMF Input} {target predict : Input → Output} {q : ℝ≥0∞}
    (region : Finset Input)
    (hbound : agreementMass μ target predict ≤ q)
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧ predict x ≠ target x := by
  exact
    exists_pos_mass_disagreement_in_region_of_agreementMass_lt_regionMass
      (μ := μ) (target := target) (predict := predict) region
      (lt_of_le_of_lt hbound hmass)

/-- If agreement mass is one, then the predictors agree on the whole positive
mass support. -/
theorem agrees_on_support_of_agreementMass_eq_one
    {μ : PMF Input} {target predict : Input → Output}
    (hone : agreementMass μ target predict = 1) :
    ∀ x, μ x ≠ 0 → predict x = target x := by
  intro x hx
  have hmeasure :
      μ.toOuterMeasure {y | predict y = target y} = 1 := by
    simpa [agreementMass_eq_toOuterMeasure_agreementSet] using hone
  have hsupport :
      μ.support ⊆ {y | predict y = target y} :=
    (μ.toOuterMeasure_apply_eq_one_iff
      (s := {y | predict y = target y})).1 hmeasure
  exact hsupport ((μ.mem_support_iff x).2 hx)

/-- A positive-mass disagreement rules out perfect agreement mass. -/
theorem agreementMass_ne_one_of_pos_mass_disagreement
    {μ : PMF Input} {target predict : Input → Output} {x : Input}
    (hxμ : μ x ≠ 0)
    (hdisagree : predict x ≠ target x) :
    agreementMass μ target predict ≠ 1 := by
  intro hone
  exact hdisagree (agrees_on_support_of_agreementMass_eq_one hone x hxμ)

/-- Agreement mass is always at most one. -/
theorem agreementMass_le_one
    (μ : PMF Input) (target predict : Input → Output) :
    agreementMass μ target predict ≤ 1 := by
  classical
  rw [agreementMass_eq_toOuterMeasure_agreementSet]
  calc
    μ.toOuterMeasure {x | predict x = target x}
        ≤ μ.toOuterMeasure (Set.univ : Set Input) :=
      μ.toOuterMeasure_mono (Set.subset_univ _)
    _ = 1 := by
      rw [μ.toOuterMeasure_apply_eq_one_iff]
      exact Set.subset_univ _

/-- A positive-mass disagreement makes agreement mass strictly less than one. -/
theorem agreementMass_lt_one_of_pos_mass_disagreement
    {μ : PMF Input} {target predict : Input → Output} {x : Input}
    (hxμ : μ x ≠ 0)
    (hdisagree : predict x ≠ target x) :
    agreementMass μ target predict < 1 := by
  exact lt_of_le_of_ne
    (agreementMass_le_one μ target predict)
    (agreementMass_ne_one_of_pos_mass_disagreement hxμ hdisagree)

/-- Under an atomic distribution, a matching atom has agreement mass one. -/
theorem agreementMass_pure_eq_one_of_agrees
    {x : Input} {target predict : Input → Output}
    (hagree : predict x = target x) :
    agreementMass (PMF.pure x) target predict = 1 := by
  classical
  rw [agreementMass_eq_sum_indicator]
  calc
    (∑ a : Input, if predict a = target a then PMF.pure x a else 0)
        = ∑ a : Input, if a = x then (1 : ℝ≥0∞) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hax : a = x
          · subst a
            simp [hagree]
          · simp [PMF.pure_apply, hax]
    _ = 1 := by simp

/-- Under an atomic distribution, a disagreeing atom has agreement mass zero. -/
theorem agreementMass_pure_eq_zero_of_disagrees
    {x : Input} {target predict : Input → Output}
    (hdisagree : predict x ≠ target x) :
    agreementMass (PMF.pure x) target predict = 0 := by
  classical
  rw [agreementMass_eq_sum_indicator]
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases hax : a = x
  · subst a
    simp [hdisagree]
  · simp [PMF.pure_apply, hax]

/-- The product mass of one length-`m` point sample under independent draws from `μ`. -/
noncomputable def sampleMass
    (μ : PMF Input) {m : ℕ} (sample : PointSample Input m) : ℝ≥0∞ :=
  ∏ i, μ (sample i)

/-- The total mass of length-`m` samples on which `predict` agrees with `target`
at every sampled point. -/
noncomputable def consistentSampleMass
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : ConsistentSamples target predict m, sampleMass μ sample.1

noncomputable instance instDecidableAgreesWithTarget
    (target predict : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (AgreesWithTarget target predict sample) := by
  classical
  unfold AgreesWithTarget
  infer_instance

/-- Consistent sample mass as a full sample-space indicator sum. -/
theorem consistentSampleMass_eq_sum_indicator
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) :
    consistentSampleMass μ target predict m =
      ∑ sample : PointSample Input m,
        if AgreesWithTarget target predict sample then sampleMass μ sample else 0 := by
  classical
  unfold consistentSampleMass
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (PointSample Input m)))
      (f := fun sample : PointSample Input m => sampleMass μ sample)
      (p := fun sample => AgreesWithTarget target predict sample))

theorem consistentSampleMass_eq_agreementMass_pow
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) :
    consistentSampleMass μ target predict m = agreementMass μ target predict ^ m := by
  classical
  unfold consistentSampleMass agreementMass sampleMass
  calc
    (∑ sample : ConsistentSamples target predict m, ∏ i, μ (sample.1 i))
      = ∑ g : Fin m → AgreementPoints target predict, ∏ i, μ (g i).1 := by
          refine Fintype.sum_equiv
            (consistentSamplesEquivAgreementFunctions target predict m)
            (fun sample : ConsistentSamples target predict m => ∏ i, μ (sample.1 i))
            (fun g : Fin m → AgreementPoints target predict => ∏ i, μ (g i).1)
            ?_
          intro sample
          rfl
    _ = (∑ a : AgreementPoints target predict, μ a.1) ^ m := by
          symm
          simpa using
            (Finset.sum_pow'
              (s := Finset.univ)
              (f := fun a : AgreementPoints target predict => μ a.1)
              (n := m))

theorem consistentSampleMass_le_pow_of_agreementMass_le
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) {q : ℝ≥0∞}
    (hq : agreementMass μ target predict ≤ q) :
    consistentSampleMass μ target predict m ≤ q ^ m := by
  rw [consistentSampleMass_eq_agreementMass_pow]
  exact (pow_left_mono m) hq

/-- If `predict` agrees with `target` on a finite region, then IID samples drawn
entirely from that region give a lower bound on the consistent-sample mass. -/
theorem regionMass_pow_le_consistentSampleMass_of_agrees_on
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → predict x = target x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤ consistentSampleMass μ target predict m := by
  rw [consistentSampleMass_eq_agreementMass_pow]
  exact (pow_left_mono m)
    (finset_mass_le_agreementMass_of_agrees_on
      (μ := μ) (target := target) (predict := predict) region hagree)

end WeightedAgreement

end Mettapedia.Computability.PNP
