import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatIdentitySampleKernelObstruction

/-!
# Identity-Anchor Sample-Kernel Specialization of the General Linear Shift-Kernel Obstruction

This file shows that the newer general finite shift-kernel shell subsumes the
older identity-anchor sampled-kernel sum law.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelIdentitySampleSpecialization

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

def SeedLiveSampleKernel.identityShiftKernel (K : SeedLiveSampleKernel κ X) :
    SeedLiveShiftKernel κ X where
  seedShift := fun _ => 0
  liveShift := fun _ => 0
  seedCoeff := K.seedCoeff
  liveCoeff := K.liveCoeff

theorem SeedLiveShiftKernel.seedCoeffSumAt_identityShiftKernel_zero_eq_seedCoeffSum
    (K : SeedLiveSampleKernel κ X) :
    SeedLiveShiftKernel.seedCoeffSumAt K.identityShiftKernel 0 =
      K.seedCoeffSum := by
  unfold SeedLiveShiftKernel.seedCoeffSumAt
    SeedLiveSampleKernel.identityShiftKernel
    SeedLiveSampleKernel.seedCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

theorem SeedLiveShiftKernel.liveCoeffSumAt_identityShiftKernel_zero_eq_liveCoeffSum
    (K : SeedLiveSampleKernel κ X) :
    SeedLiveShiftKernel.liveCoeffSumAt K.identityShiftKernel 0 =
      K.liveCoeffSum := by
  unfold SeedLiveShiftKernel.liveCoeffSumAt
    SeedLiveSampleKernel.identityShiftKernel
    SeedLiveSampleKernel.liveCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

omit [DecidableEq X] in
theorem WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors
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
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  funext y
  unfold WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice
    WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice
    UniformVorticityTendril.seedLiveOperatorInitialSlice
  simp [SeedLiveSampleKernel.identityShiftKernel,
    SeedLiveShiftKernel.toSampleKernel,
    SeedLiveSampleKernel.toSeedLiveOperator,
    hseed, hlive, add_zero]

omit [DecidableEq X] in
theorem WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors_of_componentwise_abs_le
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
    (x : ModeState)
    (hK : K.IdentityAnchors) :
    L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K.identityShiftKernel c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  funext y
  unfold WeightedObservable.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
    WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
    UniformVorticityTendril.seedLiveOperatorInitialSlice
  simp [SeedLiveSampleKernel.identityShiftKernel,
    SeedLiveShiftKernel.toSampleKernel,
    SeedLiveSampleKernel.toSeedLiveOperator,
    hseed, hlive, add_zero]

omit [DecidableEq X] in
theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_eq_shiftKernelCandidate_of_identityAnchors
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
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  unfold WeightedObservable.windowedColeHopfHeatSampleKernelCandidate
    WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate
  congr
  funext t y
  simp [SeedLiveSampleKernel.identityShiftKernel,
    SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    hseed, hlive, add_zero]

omit [DecidableEq X] in
theorem WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_eq_shiftKernelCandidate_of_identityAnchors_of_componentwise_abs_le
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
    (x : ModeState)
    (hK : K.IdentityAnchors) :
    L.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K.identityShiftKernel c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  rcases hK with ⟨hseed, hlive⟩
  unfold WeightedObservable.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
    WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
    UniformVorticityTendril.seedLiveOperatorCandidate
  congr
  funext t y
  simp [SeedLiveSampleKernel.identityShiftKernel,
    SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    hseed, hlive, add_zero]

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernel_sum_eq_one_of_topDownBridge_via_generalShiftKernel
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
  have hInitEq :=
    L.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK
  have hCandEq :=
    L.windowedColeHopfHeatSampleKernelCandidate_eq_shiftKernelCandidate_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK
  let B' :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
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
      compatibility := B.compatibility }
  have hCand' :
      B'.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    change B.candidate =
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    simpa [hCandEq] using hCand
  rcases hnz with ⟨y, hy⟩
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
      SeedLiveShiftKernel.seedCoeffSumAt K.identityShiftKernel 0 +
        SeedLiveShiftKernel.liveCoeffSumAt K.identityShiftKernel 0 = 1 :=
    L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_eq_one_of_topDownBridge_of_zero_other_anchors_nonzero_initial
      (ι := ι) (X := X)
      selector K.identityShiftKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B' hCand' hseedOther hliveOther hy
  simpa [SeedLiveShiftKernel.seedCoeffSumAt_identityShiftKernel_zero_eq_seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSumAt_identityShiftKernel_zero_eq_liveCoeffSum,
      SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum, add_comm] using hsum

theorem WeightedObservable.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_of_sum_ne_one_of_nonzero_initial_via_generalShiftKernel
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
    L.windowedColeHopfHeatIdentitySampleKernel_sum_eq_one_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK B hCand hnz

end WindowedColeHopfHeatGeneralShiftKernelIdentitySampleSpecialization

end NavierStokes
end FluidDynamics
end Mettapedia
