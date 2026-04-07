import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatIdentitySampleKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Saturated Obstruction for Identity-Anchor Sample Kernels

This file pushes the nonlinear saturated obstruction one step beyond the
diagonal sampled-kernel case. If a finite sampled kernel keeps both seed and
live anchors equal to the identity, then any top-down bridge equating that
sampled-kernel route with the concrete saturated descendant forces the same
constant-magnitude rigidity as in the diagonal case.

So finite repetition at the same point does not rescue the saturated route
either: once the anchors collapse to the identity, the only same-route bridges
are those compatible with a constant nonzero initial magnitude.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedIdentitySampleKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
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
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    (K.liveCoeffSum + K.seedCoeffSum) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y|) = a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity 1 y
  have hcompat :
      sampleKernelCompatibilityPred (Time := NNReal) (X := X) K T
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hEq :
      a * (w / (1 + |w|)) = K.liveCoeffSum * w + K.seedCoeffSum * w := by
    calc
      a * (w / (1 + |w|))
          = (L.windowedColeHopfHeatSaturatedCandidate
              (ι := ι) (X := X)
              selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity 1 y := by
                change a * (T.vorticity 1 y / (1 + |T.vorticity 1 y|)) =
                  (T.saturatedCandidate a).velocity 1 y
                rfl
      _ = (L.windowedColeHopfHeatSampleKernelCandidate
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity 1 y := by
                simpa using hcompat 1 y
      _ = (L.windowedColeHopfHeatSeedBlendCandidate
              (ι := ι) (X := X)
              selector K.liveCoeffSum K.seedCoeffSum c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity 1 y := by
                simpa [L.windowedColeHopfHeatSampleKernelCandidate_eq_seedBlendCandidate_of_identityAnchors
                  (ι := ι) (X := X)
                  selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK]
      _ = K.liveCoeffSum * w + K.seedCoeffSum * w := by
            change (T.seedBlendCandidate K.liveCoeffSum K.seedCoeffSum).velocity 1 y =
              K.liveCoeffSum * w + K.seedCoeffSum * w
            simp [UniformVorticityTendril.seedBlendCandidate, w]
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hmul : a * w = (((K.liveCoeffSum + K.seedCoeffSum) * (1 + |w|)) * w) := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = (K.liveCoeffSum * w + K.seedCoeffSum * w) * (1 + |w|) := by rw [hEq]
      _ = (((K.liveCoeffSum + K.seedCoeffSum) * (1 + |w|)) * w) := by ring
  have hzero : (a - (K.liveCoeffSum + K.seedCoeffSum) * (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
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
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁| =
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂| := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have h1 :
      (K.liveCoeffSum + K.seedCoeffSum) * (1 + |T.vorticity 1 y₁|) = a :=
    L.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₁
  have h2 :
      (K.liveCoeffSum + K.seedCoeffSum) * (1 + |T.vorticity 1 y₂|) = a :=
    L.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₂
  have hsum_ne : K.liveCoeffSum + K.seedCoeffSum ≠ 0 := by
    intro hsum
    have : 0 = a := by simpa [hsum] using h1
    exact ha this.symm
  have hzero :
      (K.liveCoeffSum + K.seedCoeffSum) *
        (|T.vorticity 1 y₁| - |T.vorticity 1 y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hsum | habs
  · exact False.elim (hsum_ne hsum)
  · linarith

theorem WeightedObservable.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hwitness :
      ∃ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial
      (ι := ι) (X := X) selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₁ hnz₂
  exact habs hEq

end WindowedColeHopfHeatSaturatedIdentitySampleKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
