import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatMaskedShiftKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Saturated Obstruction for the Finite Masked Shift-Kernel Family

This file shows that the concrete nonlinear saturated descendant does not fit
the widened finite masked shift-kernel shell except in rigid special cases.

The masked shift family already collapses to the anchored three-coefficient
spatial route, so the nonlinear obstruction can be stated directly in terms of
the total unshifted-live mass.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedMaskedShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff))
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
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0)
    (hshift :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 +
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y|) = a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let w := T.vorticity t y
  have hcompat :
      shiftKernelCompatibilityPred (Time := NNReal) (X := X)
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff)
        T
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hcompatShift :
      (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y =
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
    simpa [shiftKernelCompatibilityPred, sampleKernelCompatibilityPred,
      seedLiveOperatorCompatibilityPred, WeightedObservable.windowedColeHopfHeatShiftKernelCandidate]
      using hcompat t y
  have hcompatAnchored :
      (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y =
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s
          (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
          (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
          (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
    simpa using congrArg (fun C : VelocityPressureCandidate (Time := NNReal) (X := X) => C.velocity t y)
      (L.windowedColeHopfHeatShiftKernelCandidate_eq_anchoredShiftCandidate_of_maskedAnchoredTranslation
        (ι := ι) (X := X)
        selector mask s seedCoeff liveCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x)
  have hEq :
      a * (w / (1 + |w|)) =
        SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * w +
          SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff * T.vorticity 1 (y + s) +
          SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff * T.vorticity t (y + s) := by
    calc
      a * (w / (1 + |w|)) =
          (L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
              rfl
      _ =
          (L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := hcompatShift
      _ =
          (L.windowedColeHopfHeatAnchoredShiftCandidate
            (ι := ι) (X := X)
            selector s
            (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
            (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
            (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := hcompatAnchored
      _ = SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * w +
            SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff * T.vorticity 1 (y + s) +
            SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff * T.vorticity t (y + s) := by
            simp [w, T, WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate,
              UniformVorticityTendril.seedLiveOperatorCandidate, anchoredSeedLiveBlendOperator]
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hEq' :
      a * (w / (1 + |w|)) =
        SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * w := by
    simpa [T, hseed, hshift] using hEq
  have hmul :
      a * w =
        (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 + |w|)) * w := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * w) * (1 + |w|) := by
        rw [hEq']
      _ = (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 + |w|)) * w := by
        ring
  have hzero :
      (a - SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hw
  · linarith
  · exact False.elim (hnz hw)

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_shifted_witnesses
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff))
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
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₁ + s) = 0)
    (hshift₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ (y₁ + s) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hseed₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y₂ + s) = 0)
    (hshift₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ (y₂ + s) = 0)
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
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 + |T.vorticity t₁ y₁|) = a :=
    L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₁ hshift₁ hnz₁
  have h2 :
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 + |T.vorticity t₂ y₂|) = a :=
    L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₂ hshift₂ hnz₂
  have hbase_ne : SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff ≠ 0 := by
    intro hbase
    have : 0 = a := by simpa [hbase] using h1
    exact ha this.symm
  have hzero :
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff *
        (|T.vorticity t₁ y₁| - |T.vorticity t₂ y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hbase | habs
  · exact False.elim (hbase_ne hbase)
  · linarith

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff))
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
    L.windowedColeHopfHeatMaskedShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_shifted_witnesses
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed₁ hshift₁ hnz₁ hseed₂ hshift₂ hnz₂
  exact habs hEq

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff))
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
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
        (y + s) = 0)
    (hshift :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
        (y + s) = 0)
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff * (1 +
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
      (L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
        (ι := ι) (X := X)
        selector mask s seedCoeff liveCoeff a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseed hshift hnz)

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_shifted_witnesses_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff))
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
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
        (y₁ + s) = 0)
    (hshift₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁
        (y₁ + s) = 0)
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hseed₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
        (y₂ + s) = 0)
    (hshift₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂
        (y₂ + s) = 0)
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
      (L.windowedColeHopfHeatMaskedShiftKernel_abs_eq_abs_of_topDownBridge_of_two_zero_shifted_witnesses
        (ι := ι) (X := X)
        selector mask s seedCoeff liveCoeff a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseed₁ hshift₁ hnz₁ hseed₂ hshift₂ hnz₂)

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
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
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₁ + s) = 0) ∧
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁
          (y₁ + s) = 0) ∧
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0) ∧
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₂ + s) = 0) ∧
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂
          (y₂ + s) = 0) ∧
        ((L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) ∧
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
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff))
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
      (L.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses
        (ι := ι) (X := X)
        selector mask s seedCoeff liveCoeff a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

end WindowedColeHopfHeatSaturatedMaskedShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
