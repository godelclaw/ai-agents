import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Constant-Magnitude Saturated Shift-Kernel Frontier

This file records the first honest constructive survivor for the nonlinear
saturated route inside the full finite shift-kernel shell.

If the concrete windowed vorticity tendril has constant absolute magnitude `r`
at every time and point, then the saturated candidate is exactly a zero-shift
live-only kernel with coefficient `a / (1 + r)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitudeFrontier

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

/-- The minimal linear shell that can realize the saturated candidate in the
constant-magnitude regime: zero seed contribution, zero spatial shift, and a
single live coefficient `a / (1 + r)`. -/
def saturatedConstantMagnitudeShiftKernel (X : Type*) [AddMonoid X] (a r : ℝ) :
    SeedLiveShiftKernel Unit X :=
  diagonalShiftKernel (X := X) 0 0 (a / (1 + r))

theorem WeightedObservable.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelInitialSlice_eq_saturatedInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  funext y
  have hmag : |T.vorticity 1 y| = r := habs y
  have hbase :
      L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x y
        =
      (a / (1 + r)) *
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y := by
    simp [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice,
      saturatedConstantMagnitudeShiftKernel, diagonalShiftKernel,
      UniformVorticityTendril.seedLiveOperatorInitialSlice,
      SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
      add_zero]
  calc
    L.windowedColeHopfHeatShiftKernelInitialSlice
        (ι := ι) (X := X)
        selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x y
      = (a / (1 + r)) * T.vorticity 1 y := by
          simpa [T] using hbase
    _ = a * (T.vorticity 1 y / (1 + r)) := by
          ring
    _ = a * (T.vorticity 1 y / (1 + |T.vorticity 1 y|)) := by
          rw [hmag]
    _ = T.saturatedInitialSlice a y := rfl

theorem WeightedObservable.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelCandidate_eq_saturatedCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  unfold WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    WeightedObservable.windowedColeHopfHeatSaturatedCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate UniformVorticityTendril.saturatedCandidate
  congr
  funext t y
  simp [saturatedConstantMagnitudeShiftKernel, diagonalShiftKernel,
    SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    add_zero]
  have hmag : |T.vorticity t y| = r := habs t y
  calc
    (a / (1 + r)) * T.vorticity t y = a * (T.vorticity t y / (1 + r)) := by
      ring
    _ = a * (T.vorticity t y / (1 + |T.vorticity t y|)) := by
      rw [hmag]

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) (saturatedConstantMagnitudeShiftKernel X a r))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
    curlFrame curlBound curlBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelCandidate_eq_saturatedCandidate
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

end WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitudeFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
