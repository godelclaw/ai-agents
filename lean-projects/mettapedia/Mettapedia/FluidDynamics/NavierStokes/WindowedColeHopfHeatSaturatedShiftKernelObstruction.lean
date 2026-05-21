import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Saturated Obstruction for the Finite Shift-Kernel Shell

This file lifts the nonlinear saturated obstruction from the masked common-shift
family to arbitrary finite translation kernels.  The witness pattern requires
all seeded anchors to vanish and every nonzero live anchor to vanish, leaving
only the total zero-shift live mass.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

namespace SeedLiveShiftKernel

/-- Total live mass sitting at the unshifted anchor. -/
def liveZeroCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  ∑ i, if K.liveShift i = 0 then K.liveCoeff i else 0

end SeedLiveShiftKernel

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hseed :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hshift :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.liveZeroCoeffSum K * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y|) = a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity t y
  have hcompat :
      shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
        T
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hEq :
      a * (w / (1 + |w|)) =
        ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity t (y + K.liveShift i)) := by
    simpa [w, shiftKernelCompatibilityPred, sampleKernelCompatibilityPred,
      seedLiveOperatorCompatibilityPred,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate,
      SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator]
      using hcompat t y
  have hEq' :
      a * (w / (1 + |w|)) =
        ∑ i, (if K.liveShift i = 0 then K.liveCoeff i else 0) * w := by
    calc
      a * (w / (1 + |w|))
          = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
              K.liveCoeff i * T.vorticity t (y + K.liveShift i)) := hEq
      _ = ∑ i, ((if K.liveShift i = 0 then K.liveCoeff i else 0) * w) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseed i
            by_cases h0 : K.liveShift i = 0
            · simp [hseed_i, h0, w]
            · have hshift_i : T.vorticity t (y + K.liveShift i) = 0 := hshift i h0
              simp [hseed_i, h0, hshift_i]
  have hEq'' :
      a * (w / (1 + |w|)) = SeedLiveShiftKernel.liveZeroCoeffSum K * w := by
    rw [SeedLiveShiftKernel.liveZeroCoeffSum]
    calc
      a * (w / (1 + |w|))
          = ∑ i, (if K.liveShift i = 0 then K.liveCoeff i else 0) * w := hEq'
      _ = (∑ i, if K.liveShift i = 0 then K.liveCoeff i else 0) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => if K.liveShift i = 0 then K.liveCoeff i else 0)
                (a := w)).symm
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hmul :
      a * w = (SeedLiveShiftKernel.liveZeroCoeffSum K * (1 + |w|)) * w := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = (SeedLiveShiftKernel.liveZeroCoeffSum K * w) * (1 + |w|) := by
        rw [hEq'']
      _ = (SeedLiveShiftKernel.liveZeroCoeffSum K * (1 + |w|)) * w := by
        ring
  have hzero : (a - SeedLiveShiftKernel.liveZeroCoeffSum K * (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {y : X}
    (hseedOther :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hliveOther :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y|) = a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity 1 y
  have hcompat :
      shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
        T
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hEq :
      a * (w / (1 + |w|)) =
        ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)) := by
    simpa [w, shiftKernelCompatibilityPred, sampleKernelCompatibilityPred,
      seedLiveOperatorCompatibilityPred,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate,
      SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator]
      using hcompat 1 y
  have hEq' :
      a * (w / (1 + |w|)) =
        (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * w := by
    calc
      a * (w / (1 + |w|))
          = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
              K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)) := hEq
      _ = ∑ i, (((if K.seedShift i = 0 then K.seedCoeff i else 0) +
              (if K.liveShift i = 0 then K.liveCoeff i else 0)) * w) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hseed0 : K.seedShift i = 0
            · by_cases hlive0 : K.liveShift i = 0
              · simp [hseed0, hlive0, w, add_mul]
              · have hlive_i : T.vorticity 1 (y + K.liveShift i) = 0 := hliveOther i hlive0
                simp [hseed0, hlive0, hlive_i, w]
            · have hseed_i : T.vorticity 1 (y + K.seedShift i) = 0 := hseedOther i hseed0
              by_cases hlive0 : K.liveShift i = 0
              · simp [hseed0, hlive0, hseed_i, w]
              · have hlive_i : T.vorticity 1 (y + K.liveShift i) = 0 := hliveOther i hlive0
                simp [hseed0, hlive0, hseed_i, hlive_i]
      _ = (∑ i, ((if K.seedShift i = 0 then K.seedCoeff i else 0) +
              (if K.liveShift i = 0 then K.liveCoeff i else 0))) * w := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ =>
                  (if K.seedShift i = 0 then K.seedCoeff i else 0) +
                    (if K.liveShift i = 0 then K.liveCoeff i else 0))
                (a := w)).symm
      _ = ((∑ i, if K.seedShift i = 0 then K.seedCoeff i else 0) +
            (∑ i, if K.liveShift i = 0 then K.liveCoeff i else 0)) * w := by
            rw [Finset.sum_add_distrib]
      _ = (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * w := by
            simp [SeedLiveShiftKernel.seedCoeffSumAt, SeedLiveShiftKernel.liveCoeffSumAt]
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hmul :
      a * w =
        ((SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
          (1 + |w|)) * w := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = ((SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * w) *
            (1 + |w|) := by
            rw [hEq']
      _ = ((SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
            (1 + |w|)) * w := by
            ring
  have hzero :
      (a - (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
        (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_seed_nonzero_shift_witnesses
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hseed₁ :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₁ + K.seedShift i) = 0)
    (hshift₁ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁
          (y₁ + K.liveShift i) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hseed₂ :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₂ + K.seedShift i) = 0)
    (hshift₂ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂
          (y₂ + K.liveShift i) = 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have h1 :
      SeedLiveShiftKernel.liveZeroCoeffSum K * (1 + |T.vorticity t₁ y₁|) = a :=
    L.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₁ hshift₁ hnz₁
  have h2 :
      SeedLiveShiftKernel.liveZeroCoeffSum K * (1 + |T.vorticity t₂ y₂|) = a :=
    L.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₂ hshift₂ hnz₂
  have hzero_ne : SeedLiveShiftKernel.liveZeroCoeffSum K ≠ 0 := by
    intro hzero
    have : 0 = a := by simpa [hzero] using h1
    exact ha this.symm
  have hzero :
      SeedLiveShiftKernel.liveZeroCoeffSum K *
        (|T.vorticity t₁ y₁| - |T.vorticity t₂ y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hzero' | habs
  · exact False.elim (hzero_ne hzero')
  · linarith

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_other_anchors_nonzero_initials
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {y₁ y₂ : X}
    (hseedOther₁ :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₁ + K.seedShift i) = 0)
    (hliveOther₁ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₁ + K.liveShift i) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0)
    (hseedOther₂ :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₂ + K.seedShift i) = 0)
    (hliveOther₂ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₂ + K.liveShift i) = 0)
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
      (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
        (1 + |T.vorticity 1 y₁|) = a :=
    L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseedOther₁ hliveOther₁ hnz₁
  have h2 :
      (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
        (1 + |T.vorticity 1 y₂|) = a :=
    L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial
      (ι := ι) (X := X) selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseedOther₂ hliveOther₂ hnz₂
  have hsum_ne :
      SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0 ≠ 0 := by
    intro hsum
    have : 0 = a := by simpa [hsum] using h1
    exact ha this.symm
  have hzero :
      (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) *
        (|T.vorticity 1 y₁| - |T.vorticity 1 y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hsum | habs
  · exact False.elim (hsum_ne hsum)
  · linarith

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₁ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁
            (y₁ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₂ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂
            (y₂ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t₁, y₁, t₂, y₂, hseed₁, hshift₁, hnz₁, hseed₂, hshift₂, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_seed_nonzero_shift_witnesses
      (ι := ι) (X := X)
      selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₁ hshift₁ hnz₁ hseed₂ hshift₂ hnz₂
  exact habs hEq

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_other_anchors_nonzero_initials
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
        (∀ i : κ, K.seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₁ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₁ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0 ∧
        (∀ i : κ, K.seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₂ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
            (y₂ + K.liveShift i) = 0) ∧
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
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨y₁, y₂, hseedOther₁, hliveOther₁, hnz₁, hseedOther₂, hliveOther₂, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_other_anchors_nonzero_initials
      (ι := ι) (X := X)
      selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseedOther₁ hliveOther₁ hnz₁ hseedOther₂ hliveOther₂ hnz₂
  exact habs hEq

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsat : satCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₁ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y₂ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  rcases hwitness with
    ⟨t₁, y₁, t₂, y₂, hseed₁_zero, hseed₁_shift, hlive₁_shift, hnz₁,
      hseed₂_zero, hseed₂_shift, hlive₂_shift, hnz₂, habs⟩
  refine
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsat hc hν curlFrame curlBound curlBound_nonneg hcurl x ?_
  refine ⟨t₁, y₁, t₂, y₂, ?_, ?_, hnz₁, ?_, ?_, hnz₂, habs⟩
  · intro i
    fin_cases i <;> simp [anchoredTranslationShiftKernel, hseed₁_zero, hseed₁_shift]
  · intro i hi
    fin_cases i
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · simpa [anchoredTranslationShiftKernel] using hlive₁_shift
  · intro i
    fin_cases i <;> simp [anchoredTranslationShiftKernel, hseed₂_zero, hseed₂_shift]
  · intro i hi
    fin_cases i
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · exact False.elim (hi (by simp [anchoredTranslationShiftKernel]))
    · simpa [anchoredTranslationShiftKernel] using hlive₂_shift

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {y : X}
    (hseedOther :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hliveOther :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    (SeedLiveShiftKernel.seedCoeffSumAt K 0 + SeedLiveShiftKernel.liveCoeffSumAt K 0) * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y|) = a := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatShiftKernel_zeroAnchorCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_other_anchors_nonzero_initial
        (ι := ι) (X := X) selector K a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseedOther hliveOther hnz)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_other_anchors_nonzero_initials_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {y₁ y₂ : X}
    (hseedOther₁ :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₁ + K.seedShift i) = 0)
    (hliveOther₁ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₁ + K.liveShift i) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0)
    (hseedOther₂ :
      ∀ i : κ, K.seedShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₂ + K.seedShift i) = 0)
    (hliveOther₂ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₂ + K.liveShift i) = 0)
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
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_other_anchors_nonzero_initials
        (ι := ι) (X := X) selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseedOther₁ hliveOther₁ hnz₁ hseedOther₂ hliveOther₂ hnz₂)

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_other_anchors_nonzero_initials_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
        (∀ i : κ, K.seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₁ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₁ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁ ≠ 0 ∧
        (∀ i : κ, K.seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₂ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₂ + K.liveShift i) = 0) ∧
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
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_other_anchors_nonzero_initials
        (ι := ι) (X := X) selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hseed :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y + K.seedShift i) = 0)
    (hshift :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.liveZeroCoeffSum K * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y|) = a := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness
        (ι := ι) (X := X) selector K a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseed hshift hnz)

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_seed_nonzero_shift_witnesses_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
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
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hseed₁ :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₁ + K.seedShift i) = 0)
    (hshift₁ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁
          (y₁ + K.liveShift i) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hseed₂ :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₂ + K.seedShift i) = 0)
    (hshift₂ :
      ∀ i : κ, K.liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂
          (y₂ + K.liveShift i) = 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| =
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂| := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_seed_nonzero_shift_witnesses
        (ι := ι) (X := X) selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseed₁ hshift₁ hnz₁ hseed₂ hshift₂ hnz₂)

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₁ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁
            (y₁ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (∀ i : κ,
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
            (y₂ + K.seedShift i) = 0) ∧
        (∀ i : κ, K.liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂
            (y₂ + K.liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses
        (ι := ι) (X := X) selector K a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsat : satCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₁ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 y₂ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1 (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  simpa [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs
        (ι := ι) (X := X) selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsat hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

end WindowedColeHopfHeatSaturatedShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
