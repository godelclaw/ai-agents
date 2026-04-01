import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfHeatFeffermanInterface
import Mettapedia.FluidDynamics.NavierStokes.WindowedCutoffApproximation

/-!
# Windowed Cole-Hopf Heat Package

This file shows that a genuine smooth window cutoff can still satisfy the
quantitative hypotheses needed by the current positive heat-decayed Cole-Hopf
route.

So the window leaving the stricter `EnergyProfile` shell is not yet a failure
of the present approximation-and-envelope package.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatPackage

variable {ι X : Type*}
variable [Fintype ι]

theorem smoothWindowCutoff_eq_zero_of_le_neg_inv
    {c u : ℝ} (hc : 0 < c) (hu : u ≤ -c⁻¹) :
    smoothWindowCutoff c u = 0 := by
  unfold smoothWindowCutoff
  have hc_nonneg : 0 ≤ c := hc.le
  have hcu1 : c * u + 1 ≤ 0 := by
    have hmul : c * u ≤ c * (-c⁻¹) := mul_le_mul_of_nonneg_left hu hc_nonneg
    have hbase : c * (-c⁻¹) = -1 := by
      field_simp [ne_of_gt hc]
    linarith [hmul]
  have hcu : c * u ≤ 0 := by
    have hmul : c * u ≤ c * (-c⁻¹) := mul_le_mul_of_nonneg_left hu hc_nonneg
    have hbase : c * (-c⁻¹) = -1 := by
      field_simp [ne_of_gt hc]
    linarith [hmul]
  rw [Real.smoothTransition.zero_of_nonpos hcu1, Real.smoothTransition.zero_of_nonpos hcu]
  ring

theorem smoothWindowCutoff_eq_zero_of_inv_le
    {c u : ℝ} (hc : 0 < c) (hu : c⁻¹ ≤ u) :
    smoothWindowCutoff c u = 0 := by
  unfold smoothWindowCutoff
  have hcu : 1 ≤ c * u := by
    have hmul : c * c⁻¹ ≤ c * u := mul_le_mul_of_nonneg_left hu hc.le
    have hbase : c * c⁻¹ = 1 := by
      field_simp [ne_of_gt hc]
    linarith [hmul]
  have hcu1 : 1 ≤ c * u + 1 := by linarith
  rw [Real.smoothTransition.one_of_one_le hcu1, Real.smoothTransition.one_of_one_le hcu]
  ring

theorem abs_smoothWindowCutoff_le_inv
    {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |smoothWindowCutoff c u| ≤ c⁻¹ := by
  by_cases hlow : u ≤ -c⁻¹
  · rw [smoothWindowCutoff_eq_zero_of_le_neg_inv hc hlow]
    have hcinv_nonneg : 0 ≤ c⁻¹ := by positivity
    simpa using hcinv_nonneg
  · by_cases hhigh : c⁻¹ ≤ u
    · rw [smoothWindowCutoff_eq_zero_of_inv_le hc hhigh]
      have hcinv_nonneg : 0 ≤ c⁻¹ := by positivity
      simpa using hcinv_nonneg
    · have huabs : |u| ≤ c⁻¹ := by
        refine abs_le.mpr ?_
        constructor
        · have hlt : -c⁻¹ < u := lt_of_not_ge hlow
          linarith
        · have hlt : u < c⁻¹ := lt_of_not_ge hhigh
          linarith
      unfold smoothWindowCutoff
      have h01a0 : 0 ≤ Real.smoothTransition (c * u + 1) := Real.smoothTransition.nonneg _
      have h01a1 : Real.smoothTransition (c * u + 1) ≤ 1 := Real.smoothTransition.le_one _
      have h01b0 : 0 ≤ Real.smoothTransition (c * u) := Real.smoothTransition.nonneg _
      have h01b1 : Real.smoothTransition (c * u) ≤ 1 := Real.smoothTransition.le_one _
      have hdiff : |Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u)| ≤ 1 := by
        refine abs_le.mpr ?_
        constructor <;> linarith
      calc
        |u * (Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u))|
          = |u| * |Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u)| := by
              rw [abs_mul]
        _ ≤ |u| * 1 := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
        _ = |u| := by ring
        _ ≤ c⁻¹ := huabs

/-- The windowed cutoff satisfies the uniform boundedness hypothesis required
by the current heat-decayed Cole-Hopf package. -/
theorem smoothWindowCutoff_abs_le_inv_forall
    {c : ℝ} (hc : 0 < c) :
    ∀ u, |smoothWindowCutoff c u| ≤ c⁻¹ :=
  abs_smoothWindowCutoff_le_inv hc

/-- The current positive heat-decayed package instantiated with the genuine
smooth window cutoff. -/
def WeightedObservable.windowedColeHopfHeatSharedPackage
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound) :
    SharedApproximationPackage (Time := NNReal) (ι := ι) (X := X)
      radiusSq (matchingObservable L) :=
  L.geometricColeHopfHeatApproximation
    selector ν c⁻¹ hν (by positivity)
    (smoothWindowCutoff c)
    (continuous_smoothWindowCutoff c)
    (smoothWindowCutoff_abs_le_inv_forall hc)
    curlFrame curlBound curlBound_nonneg hcurl

/-- The corresponding concrete uniform vorticity tendril at base state `x`. -/
def WeightedObservable.windowedColeHopfHeatUniformVorticityTendril
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    UniformVorticityTendril (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatSharedPackage
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl).toUniformVorticityTendril x

theorem WeightedObservable.windowedColeHopfHeat_abs_vorticity_le_uniform
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).abs_vorticity_le_uniform

end WindowedColeHopfHeatPackage

end NavierStokes
end FluidDynamics
end Mettapedia
