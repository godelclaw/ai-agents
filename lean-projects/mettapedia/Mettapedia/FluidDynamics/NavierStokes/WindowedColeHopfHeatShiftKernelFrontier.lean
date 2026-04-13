import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveShiftKernelFrontier

/-!
# Shift-Kernel Frontier on the Windowed Cole-Hopf Heat Route

This file instantiates the finite shift-kernel seed/live frontier on the
concrete windowed heat route.

It also proves that the first concrete spatial anchored blend

`a * ω(t, x) + b * ω(1, x + s) + c * ω(t, x + s)`

is exactly a finite translation-kernel instance.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatShiftKernelFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
      K.toSampleKernel.toSeedLiveOperator

abbrev WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
      K.toSampleKernel.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_shiftKernelCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  simpa [shiftKernelCompatibilityPred] using
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
        K.toSampleKernel.toSeedLiveOperator

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_zero_vorticity
      K hzero

def WeightedObservable.toWindowedColeHopfHeatShiftKernelAlmostBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toShiftKernelAlmostBridge K

def WeightedObservable.toWindowedColeHopfHeatShiftKernelBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toShiftKernelBridge K

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
      K hcompat

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_operator_eq_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = live y) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
      K hK

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = seed y)
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
      (L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).shiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = seed y)
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
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      K hK hstat

theorem WeightedObservable.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
      K hzero

theorem WeightedObservable.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
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
  (L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

section Anchored

abbrev WeightedObservable.windowedColeHopfHeatAnchoredShiftInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
      (anchoredSeedLiveBlendOperator (X := X) (fun y => y + s) a b d)

abbrev WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
      (anchoredSeedLiveBlendOperator (X := X) (fun y => y + s) a b d)

theorem WeightedObservable.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftInitialSlice
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    UniformVorticityTendril.seedLiveOperatorInitialSlice_anchoredTranslationShiftKernel_eq_anchoredSeedLiveBlend
      (T :=
        L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (s := s) (a := a) (b := b) (c := d)

theorem WeightedObservable.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    UniformVorticityTendril.seedLiveOperatorCandidate_anchoredTranslationShiftKernel_eq_anchoredSeedLiveBlend
      (T :=
        L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (s := s) (a := a) (b := b) (c := d)

theorem WeightedObservable.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := a) (b := b) (d := d)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s a b d)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_anchoredShiftSelfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  have hEq :=
    L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have hself' :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [selfCompatibility, hEq] using hself
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := a) (b := b) (d := d)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s a b d)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself')

theorem WeightedObservable.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := a) (b := b) (d := d)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s a b d)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK)

theorem WeightedObservable.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = seed y)
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
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := a) (b := b) (d := d)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s a b d)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK hstat)

theorem WeightedObservable.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
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
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := a) (b := b) (d := d)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s a b d)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero)

end Anchored

end WindowedColeHopfHeatShiftKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
