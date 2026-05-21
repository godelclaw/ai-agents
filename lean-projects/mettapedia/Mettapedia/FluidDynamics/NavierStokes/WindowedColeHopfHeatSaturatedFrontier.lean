import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeededModel
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSaturatedPressureFrontier

/-!
# Saturated Frontier on the Windowed Cole-Hopf Heat Route

This file instantiates the generic nonlinear saturated pressure-seeded frontier
on the concrete windowed heat route.

The descendant candidate is

`u(t,x) = a * (ω(t,x) / (1 + |ω(t,x)|))`

for the concrete windowed vorticity tendril, with zero pressure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedFrontier

variable {ι X : Type*}
variable [Fintype ι]

abbrev WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a

abbrev WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).saturatedInitialSlice a

abbrev WeightedObservable.windowedColeHopfHeatSaturatedCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedCandidate a

abbrev WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).saturatedCandidate a

theorem WeightedObservable.windowedColeHopfHeatSaturatedCandidate_has_saturatedCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    saturatedCompatibilityPred (Time := NNReal) (X := X) a
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedCandidate_has_saturatedCompatibility a

theorem WeightedObservable.windowedColeHopfHeatSaturatedCandidate_has_saturatedCompatibility_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    saturatedCompatibilityPred (Time := NNReal) (X := X) a
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).saturatedCandidate_has_saturatedCompatibility a

theorem WeightedObservable.windowedColeHopfHeatSaturatedCandidate_has_selfCompatibility_of_zero
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedCandidate_has_selfCompatibility_of_zero a hzero

def WeightedObservable.toWindowedColeHopfHeatSaturatedAlmostBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSaturatedPressureSeededAlmostBridge a

def WeightedObservable.toWindowedColeHopfHeatSaturatedBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (saturatedCompatibilityPred (Time := NNReal) (X := X) a)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSaturatedPressureSeededBridge a

def WeightedObservable.toWindowedColeHopfHeatSaturatedBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
      (saturatedCompatibilityPred (Time := NNReal) (X := X) a)
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).toSaturatedPressureSeededBridge a

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSaturatedBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSaturatedBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector a c ν hc hν
    curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).realizes_clause

end WindowedColeHopfHeatSaturatedFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
