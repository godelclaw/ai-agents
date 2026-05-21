import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendObstruction
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveSampleKernelFrontier

/-!
# Sample-Kernel Frontier on the Windowed Cole-Hopf Heat Route

This file instantiates the finite sampled-kernel seed/live frontier on the
concrete windowed heat route.

It also proves that the older affine seed-blend descendant is exactly the
diagonal one-point sampled-kernel case, so the existing seed-blend rigidity
theorems remain available inside this first finite non-pointwise family.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSampleKernelFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

abbrev WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorInitialSlice
      K.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorInitialSlice
      K.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatSampleKernelCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate
      K.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorCandidate
      K.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_has_sampleKernelCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    sampleKernelCompatibilityPred (Time := NNReal) (X := X) K
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSampleKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
      K.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_has_sampleKernelCompatibility_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState) :
    sampleKernelCompatibilityPred (Time := NNReal) (X := X) K
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).velocity := by
  simpa [sampleKernelCompatibilityPred] using
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
        K.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_has_selfCompatibility_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
      (L.windowedColeHopfHeatSampleKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).sampleKernelCandidate_has_selfCompatibility_of_zero_vorticity
      K hzero

def WeightedObservable.toWindowedColeHopfHeatSampleKernelAlmostBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSampleKernelAlmostBridge K

def WeightedObservable.toWindowedColeHopfHeatSampleKernelBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSampleKernelBridge K

def WeightedObservable.toWindowedColeHopfHeatSampleKernelBridge_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
      (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).toSampleKernelBridge K

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSampleKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
        (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSampleKernelBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcompat :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility
      K hcompat

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_has_selfCompatibility_of_operator_eq_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = live y) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSampleKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).sampleKernelCandidate_has_selfCompatibility_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSampleKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).sampleKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_sampleKernel_pressure_seeded_clause_of_zero_vorticity
      K hzero

theorem WeightedObservable.toWindowedColeHopfHeatSampleKernelBridge_retains_uniform_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
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
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope :=
  (L.toWindowedColeHopfHeatSampleKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

section Diagonal

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) a b) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendInitialSlice
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorInitialSlice_diagonalSampleKernel_eq_seedBlendInitialSlice
        (a := a) (b := b)

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_seedBlendCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) a b) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_diagonalSampleKernel_eq_seedBlendCandidate
        (a := a) (b := b)

theorem WeightedObservable.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (a := a) (b := b) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause
        (ι := ι) (X := X)
        selector (diagonalSampleKernel (X := X) a b)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_seedBlendSelfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  have hEq :=
    L.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_seedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have hself' :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector (diagonalSampleKernel (X := X) a b) c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [windowedSelfCompatibility, selfCompatibility, hEq] using hself
  simpa [L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (a := a) (b := b) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility
        (ι := ι) (X := X)
        selector (diagonalSampleKernel (X := X) a b)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself')

theorem WeightedObservable.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_live_endpoint
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector (1 : ℝ) 0 c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (a := (1 : ℝ)) (b := 0) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_live
        (ι := ι) (X := X)
        selector (diagonalSampleKernel (X := X) (1 : ℝ) 0)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x (by
          intro seed live y
          simp [SeedLiveSampleKernel.toSeedLiveOperator, diagonalSampleKernel]))

theorem WeightedObservable.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (a := a) (b := b) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_zero_vorticity
        (ι := ι) (X := X)
        selector (diagonalSampleKernel (X := X) a b)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero)

theorem WeightedObservable.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_seed_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector (0 : ℝ) (1 : ℝ) c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
        (ι := ι) (X := X)
        selector (diagonalSampleKernel (X := X) (0 : ℝ) (1 : ℝ))
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
        (by
          intro seed live y
          simp [SeedLiveSampleKernel.toSeedLiveOperator, diagonalSampleKernel])
        hstat)

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_sum_eq_one_of_selfCompatibility_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector (diagonalSampleKernel (X := X) a b) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    a + b = 1 := by
  have hEq :=
    L.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_seedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have hself' :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [windowedSelfCompatibility, selfCompatibility, hEq] using hself
  exact
    L.windowedColeHopfHeatSeedBlend_sum_eq_one_of_selfCompatibility_of_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself' hnz

end Diagonal

end WindowedColeHopfHeatSampleKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
