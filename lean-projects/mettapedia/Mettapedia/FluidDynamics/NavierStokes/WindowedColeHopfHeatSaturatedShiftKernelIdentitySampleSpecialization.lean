import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelIdentitySampleSpecialization
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelObstruction

/-!
# Identity-Anchor Sample-Kernel Specialization of the General Saturated Shift-Kernel Obstruction

This file shows that the strengthened nonlinear saturated finite shift-kernel
shell subsumes the older identity-anchor sampled-kernel rigidity laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelIdentitySampleSpecialization

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_saturatedShiftKernel
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
  rcases hK with ⟨hseed, hlive⟩
  have hInitEq :=
    L.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ⟨hseed, hlive⟩
  let B' :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K.identityShiftKernel)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
    { candidate := B.candidate
      regularity := by
        simpa [hInitEq] using B.regularity
      dynamics := by
        refine
          { momentum_equation := B.dynamics.momentum_equation
            incompressible := B.dynamics.incompressible
            initial_condition := ?_ }
        simpa [hInitEq] using B.dynamics.initial_condition
      energy := by
        simpa [hInitEq] using B.energy
      compatibility := by
        refine ⟨?_⟩
        intro t z
        have hcompat := B.compatibility.vorticity_generated_by_velocity t z
        simpa [shiftKernelCompatibilityPred, sampleKernelCompatibilityPred,
          seedLiveOperatorCompatibilityPred, SeedLiveSampleKernel.identityShiftKernel,
          SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
          hseed, hlive, add_zero] using hcompat }
  have hseedOther :
      ∀ i : κ, K.identityShiftKernel.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.identityShiftKernel.seedShift i) = 0 := by
    intro i hi
    exact False.elim (hi rfl)
  have hliveOther :
      ∀ i : κ, K.identityShiftKernel.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.identityShiftKernel.liveShift i) = 0 := by
    intro i hi
    exact False.elim (hi rfl)
  have hsum :
      (SeedLiveShiftKernel.seedCoeffSumAt K.identityShiftKernel 0 +
          SeedLiveShiftKernel.liveCoeffSumAt K.identityShiftKernel 0) *
        (1 +
          |(L.windowedColeHopfHeatUniformVorticityTendril
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y|) = a :=
    L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial
      (ι := ι) (X := X)
      selector K.identityShiftKernel a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B' hCand hseedOther hliveOther hnz
  simpa [SeedLiveShiftKernel.seedCoeffSumAt_identityShiftKernel_zero_eq_seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSumAt_identityShiftKernel_zero_eq_liveCoeffSum,
      SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum, add_comm] using hsum

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_via_saturatedShiftKernel_of_two_nonzero_initial
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
    L.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_saturatedShiftKernel
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₁
  have h2 :
      (K.liveCoeffSum + K.seedCoeffSum) * (1 + |T.vorticity 1 y₂|) = a :=
    L.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_saturatedShiftKernel
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₂
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

theorem WeightedObservable.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_via_saturatedShiftKernel
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
    L.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_via_saturatedShiftKernel_of_two_nonzero_initial
      (ι := ι) (X := X)
      selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz₁ hnz₂
  exact habs hEq

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_saturatedShiftKernel_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    (K.liveCoeffSum + K.seedCoeffSum) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y|) = a := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatIdentitySampleKernel_sum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_saturatedShiftKernel
        (ι := ι) (X := X) (κ := κ)
        selector K a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hK B hCand hnz)

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_via_saturatedShiftKernel_of_two_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
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
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatIdentitySampleKernel_abs_eq_abs_of_topDownBridge_via_saturatedShiftKernel_of_two_nonzero_initial
        (ι := ι) (X := X) (κ := κ)
        selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hK B hCand hnz₁ hnz₂)

theorem WeightedObservable.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_via_saturatedShiftKernel_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
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
              selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_via_saturatedShiftKernel
        (ι := ι) (X := X) (κ := κ)
        selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hK hwitness)

end WindowedColeHopfHeatSaturatedShiftKernelIdentitySampleSpecialization

end NavierStokes
end FluidDynamics
end Mettapedia
