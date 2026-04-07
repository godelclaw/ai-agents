import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Invariant Frontier for Saturated Shift Kernels

This file records an honest constructive corridor for the nonlinear saturated
route inside the full finite shift-kernel shell.

If the concrete windowed vorticity tendril is:

- stationary between the seeded slice `t = 1` and the live slice,
- invariant under every seed and live shift used by the kernel,
- and has constant absolute magnitude `r`,

then any finite shift kernel whose total coefficient sum is `a / (1 + r)`
realizes the saturated candidate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

namespace SeedLiveShiftKernel

/-- Total seeded mass of a finite shift kernel. -/
def seedCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  ∑ i, K.seedCoeff i

/-- Total live mass of a finite shift kernel. -/
def liveCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  ∑ i, K.liveCoeff i

/-- Total coefficient mass of a finite shift kernel. -/
def totalCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  K.seedCoeffSum + K.liveCoeffSum

end SeedLiveShiftKernel

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  funext y
  calc
    L.windowedColeHopfHeatShiftKernelInitialSlice
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x y
      = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)) := by
            simp [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice,
              UniformVorticityTendril.seedLiveOperatorInitialSlice,
              SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator, T]
    _ = ∑ i, (K.seedCoeff i + K.liveCoeff i) * T.vorticity 1 y := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hseedInv i 1 y, hliveInv i 1 y]
          ring
    _ = (∑ i, (K.seedCoeff i + K.liveCoeff i)) * T.vorticity 1 y := by
          simpa using
            (Finset.sum_mul
              (s := Finset.univ)
              (f := fun i : κ => K.seedCoeff i + K.liveCoeff i)
              (a := T.vorticity 1 y)).symm
    _ = SeedLiveShiftKernel.totalCoeffSum K * T.vorticity 1 y := by
          simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
            SeedLiveShiftKernel.liveCoeffSum, Finset.sum_add_distrib, add_mul]
    _ = a * (T.vorticity 1 y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity 1 y / (1 + |T.vorticity 1 y|)) := by
          rw [habs 1 y]
    _ = T.saturatedInitialSlice a y := rfl

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  unfold WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    WeightedObservable.windowedColeHopfHeatSaturatedCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate UniformVorticityTendril.saturatedCandidate
  congr
  funext t y
  calc
    ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
        K.liveCoeff i * T.vorticity t (y + K.liveShift i))
      = ∑ i, (K.seedCoeff i + K.liveCoeff i) * T.vorticity t y := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hseedInv i 1 y, hstat t y, hliveInv i t y]
          ring
    _ = (∑ i, (K.seedCoeff i + K.liveCoeff i)) * T.vorticity t y := by
          simpa using
            (Finset.sum_mul
              (s := Finset.univ)
              (f := fun i : κ => K.seedCoeff i + K.liveCoeff i)
              (a := T.vorticity t y)).symm
    _ = SeedLiveShiftKernel.totalCoeffSum K * T.vorticity t y := by
          simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
            SeedLiveShiftKernel.liveCoeffSum, Finset.sum_add_distrib, add_mul]
    _ = a * (T.vorticity t y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity t y / (1 + |T.vorticity t y|)) := by
          rw [habs t y]

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hseedInv hliveInv hstat habs

end WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
