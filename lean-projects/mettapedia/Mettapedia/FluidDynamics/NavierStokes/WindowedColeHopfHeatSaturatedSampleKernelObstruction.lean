import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Sample-Kernel Obstruction for the Windowed Saturated Frontier

This file shows that the concrete nonlinear saturated descendant does not fit
the diagonal one-sample kernel shell except in rigid special cases.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedSampleKernelObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
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
            selector (diagonalSampleKernel (X := X) p q) c ν hc hν
            curlFrame curlBound curlBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
          (diagonalSampleKernel (X := X) p q))
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
    (p + q) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y|) = a := by
  let w :=
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y
  have hcompat :
      sampleKernelCompatibilityPred (Time := NNReal) (X := X)
        (diagonalSampleKernel (X := X) p q)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hEq : a * (w / (1 + |w|)) = p * w + q * w := by
    simpa [w, WeightedObservable.windowedColeHopfHeatSaturatedCandidate,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate,
      SeedLiveSampleKernel.toSeedLiveOperator, diagonalSampleKernel,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hcompat 1 y
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hmul : a * w = ((p + q) * (1 + |w|)) * w := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = (p * w + q * w) * (1 + |w|) := by rw [hEq]
      _ = ((p + q) * (1 + |w|)) * w := by ring
  have hzero : (a - (p + q) * (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
    (ha : a ≠ 0)
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
            selector (diagonalSampleKernel (X := X) p q) c ν hc hν
            curlFrame curlBound curlBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
          (diagonalSampleKernel (X := X) p q))
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
      (p + q) * (1 + |T.vorticity 1 y₁|) = a :=
    L.windowedColeHopfHeatDiagonalSampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X) selector p q a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz₁
  have h2 :
      (p + q) * (1 + |T.vorticity 1 y₂|) = a :=
    L.windowedColeHopfHeatDiagonalSampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X) selector p q a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz₂
  have hsum_ne : p + q ≠ 0 := by
    intro hsum
    have : 0 = a := by simpa [hsum] using h1
    exact ha this.symm
  have hzero : (p + q) * (|T.vorticity 1 y₁| - |T.vorticity 1 y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hsum | habs
  · exact False.elim (hsum_ne hsum)
  · linarith

theorem WeightedObservable.not_exists_windowedColeHopfHeatDiagonalSampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
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
              selector (diagonalSampleKernel (X := X) p q) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
            (diagonalSampleKernel (X := X) p q))
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
    L.windowedColeHopfHeatDiagonalSampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial
      (ι := ι) (X := X)
      selector p q a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz₁ hnz₂
  exact habs hEq

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector (diagonalSampleKernel (X := X) p q) c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
          (diagonalSampleKernel (X := X) p q))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    (p + q) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y|) = a := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatDiagonalSampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_nonzero_initial
        (ι := ι) (X := X)
        selector p q a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hnz)

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector (diagonalSampleKernel (X := X) p q) c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
          (diagonalSampleKernel (X := X) p q))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁| =
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₂| := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatDiagonalSampleKernel_abs_eq_abs_of_topDownBridge_of_two_nonzero_initial
        (ι := ι) (X := X)
        selector p q a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hnz₁ hnz₂)

theorem WeightedObservable.not_exists_windowedColeHopfHeatDiagonalSampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hwitness :
      ∃ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector (diagonalSampleKernel (X := X) p q) c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X)
            (diagonalSampleKernel (X := X) p q))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatDiagonalSampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
        (ι := ι) (X := X)
        selector p q a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

end WindowedColeHopfHeatSaturatedSampleKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
