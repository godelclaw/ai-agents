import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorObstruction

/-!
# Live-Only Sample/Shift Kernel Obstruction on the Windowed Cole-Hopf Heat Route

This file isolates the first genuinely live-dependent finite non-pointwise
obstruction on the concrete windowed heat route.

If a sampled kernel ignores the seeded slice entirely, then same-route closure
reduces to a pure live-sample equation.  In particular, whenever all sampled
live witnesses vanish, the target live witness must vanish too.  So any witness
with zero sampled live values but nonzero target live value rules out that
literal live-only bridge.

The same argument then specializes immediately to finite shift kernels with
zero seed coefficients.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatLiveOnlySampleKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem WeightedObservable.windowedColeHopfHeatLiveOnlySampleKernel_eq_live_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (hseedZero : ∀ i, K.seedCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X} :
    (∑ i, K.liveCoeff i *
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (K.liveAnchor i y)) =
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
  have hCandOp :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector K.toSeedLiveOperator c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa using hCand
  simpa [SeedLiveSampleKernel.toSeedLiveOperator, hseedZero] using
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_topDownBridge
      (ι := ι) (X := X)
      selector K.toSeedLiveOperator c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCandOp

theorem WeightedObservable.windowedColeHopfHeatLiveOnlySampleKernel_vorticity_eq_zero_of_topDownBridge_of_zero_sampled_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (hseedZero : ∀ i, K.seedCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hliveZero :
      ∀ i,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (K.liveAnchor i y) = 0) :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
  have hEq :=
    L.windowedColeHopfHeatLiveOnlySampleKernel_eq_live_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K hseedZero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand
      (t := t) (y := y)
  have hsumZero :
      (∑ i, K.liveCoeff i *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (K.liveAnchor i y)) = 0 := by
    simp [hliveZero]
  calc
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y
        = ∑ i, K.liveCoeff i *
            (L.windowedColeHopfHeatUniformVorticityTendril
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
              (K.liveAnchor i y) := by
                symm
                exact hEq
    _ = 0 := hsumZero

theorem WeightedObservable.not_exists_windowedColeHopfHeatLiveOnlySampleKernelTopDownBridge_of_zero_sampled_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (hseedZero : ∀ i, K.seedCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (∀ i,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (K.liveAnchor i y) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hwitness with ⟨t, y, hliveZero, hnonzero⟩
  rcases hB with ⟨B, hCand⟩
  exact hnonzero <|
    L.windowedColeHopfHeatLiveOnlySampleKernel_vorticity_eq_zero_of_topDownBridge_of_zero_sampled_live
      (ι := ι) (X := X) (κ := κ)
      selector K hseedZero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hliveZero

end WindowedColeHopfHeatLiveOnlySampleKernelObstruction

section WindowedColeHopfHeatLiveOnlyShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatLiveOnlyShiftKernel_vorticity_eq_zero_of_topDownBridge_of_zero_shifted_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hseedZero : ∀ i, K.seedCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hliveZero :
      ∀ i,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0) :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
  have hseedZeroSample : ∀ i, K.toSampleKernel.seedCoeff i = 0 := hseedZero
  have hCandSample :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K.toSampleKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa [WeightedObservable.windowedColeHopfHeatShiftKernelCandidate] using hCand
  simpa [SeedLiveShiftKernel.toSampleKernel] using
    L.windowedColeHopfHeatLiveOnlySampleKernel_vorticity_eq_zero_of_topDownBridge_of_zero_sampled_live
      (ι := ι) (X := X) (κ := κ)
      selector K.toSampleKernel hseedZeroSample c ν hc hν curlFrame curlBound curlBound_nonneg
      hcurl x B hCandSample hliveZero

theorem WeightedObservable.not_exists_windowedColeHopfHeatLiveOnlyShiftKernelTopDownBridge_of_zero_shifted_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hseedZero : ∀ i, K.seedCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (∀ i,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
            (y + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hwitness with ⟨t, y, hliveZero, hnonzero⟩
  rcases hB with ⟨B, hCand⟩
  exact hnonzero <|
    L.windowedColeHopfHeatLiveOnlyShiftKernel_vorticity_eq_zero_of_topDownBridge_of_zero_shifted_live
      (ι := ι) (X := X) (κ := κ)
      selector K hseedZero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hliveZero

end WindowedColeHopfHeatLiveOnlyShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
