import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendObstruction

/-!
# Same-Route Obstruction for Identity-Anchor Sample Kernels

This file pushes one step beyond the diagonal one-point sampled-kernel case.
If a finite sampled kernel keeps both seed and live anchors equal to the
identity, then the whole family collapses to the old affine seed-blend route
with coefficients given by the total live and seed masses.

So finite repetition at the same point does not create a new same-route escape
space: it inherits the affine bridge obstructions verbatim.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatIdentitySampleKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

def SeedLiveSampleKernel.seedCoeffSum (K : SeedLiveSampleKernel κ X) : ℝ :=
  ∑ i, K.seedCoeff i

def SeedLiveSampleKernel.liveCoeffSum (K : SeedLiveSampleKernel κ X) : ℝ :=
  ∑ i, K.liveCoeff i

def SeedLiveSampleKernel.IdentityAnchors (K : SeedLiveSampleKernel κ X) : Prop :=
  (∀ i x, K.seedAnchor i x = x) ∧ ∀ i x, K.liveAnchor i x = x

theorem WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_eq_seedBlendInitialSlice_of_identityAnchors
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
    (hK : K.IdentityAnchors) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendInitialSlice
      (ι := ι) (X := X)
      selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  funext y
  simp [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice,
    WeightedObservable.windowedColeHopfHeatSeedBlendInitialSlice,
    UniformVorticityTendril.seedLiveOperatorInitialSlice,
    UniformVorticityTendril.seedBlendInitialSlice,
    SeedLiveSampleKernel.toSeedLiveOperator,
    SeedLiveSampleKernel.seedCoeffSum, SeedLiveSampleKernel.liveCoeffSum,
    hseed, hlive, Finset.sum_add_distrib, ← Finset.sum_mul, add_comm]
  ring

theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_eq_seedBlendCandidate_of_identityAnchors
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
    (hK : K.IdentityAnchors) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendCandidate
      (ι := ι) (X := X)
      selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  unfold WeightedObservable.windowedColeHopfHeatSampleKernelCandidate
    WeightedObservable.windowedColeHopfHeatSeedBlendCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate
    UniformVorticityTendril.seedBlendCandidate
  congr
  funext t y
  simp [SeedLiveSampleKernel.toSeedLiveOperator, SeedLiveSampleKernel.seedCoeffSum,
    SeedLiveSampleKernel.liveCoeffSum, hseed, hlive, Finset.sum_add_distrib,
    ← Finset.sum_mul, add_comm]

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_sum_eq_one_of_topDownBridge_of_nonzero_initial
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
    (hK : K.IdentityAnchors)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    K.liveCoeffSum + K.seedCoeffSum = 1 := by
  have hselfSample :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfSeed :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatSampleKernelCandidate_eq_seedBlendCandidate_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK] using hselfSample
  exact
    L.windowedColeHopfHeatSeedBlend_sum_eq_one_of_selfCompatibility_of_nonzero_initial
      (ι := ι) (X := X)
      selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfSeed hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_of_sum_ne_one_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hab : K.liveCoeffSum + K.seedCoeffSum ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hab <|
    L.windowedColeHopfHeatIdentitySampleKernel_sum_eq_one_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_liveCoeffSum_eq_one_of_topDownBridge_of_zero_initial_nonzero_live
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
    (hK : K.IdentityAnchors)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    K.liveCoeffSum = 1 := by
  have hselfSample :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfSeed :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatSampleKernelCandidate_eq_seedBlendCandidate_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK] using hselfSample
  exact
    L.windowedColeHopfHeatSeedBlend_a_eq_one_of_selfCompatibility_of_zero_initial_nonzero_live
      (ι := ι) (X := X)
      selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfSeed hwitness

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_seedCoeffSum_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
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
    (hK : K.IdentityAnchors)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    K.seedCoeffSum = 0 := by
  have hselfSample :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfSeed :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatSampleKernelCandidate_eq_seedBlendCandidate_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK] using hselfSample
  exact
    L.windowedColeHopfHeatSeedBlend_b_eq_zero_of_selfCompatibility_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector K.liveCoeffSum K.seedCoeffSum c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfSeed hwitness

end WindowedColeHopfHeatIdentitySampleKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
