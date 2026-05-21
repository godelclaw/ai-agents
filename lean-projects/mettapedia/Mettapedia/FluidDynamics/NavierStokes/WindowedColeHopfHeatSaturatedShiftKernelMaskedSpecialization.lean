import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatMaskedShiftKernelObstruction

/-!
# Masked Common-Shift Specialization of the Saturated Shift-Kernel Obstruction

This file proves that the newer finite shift-kernel saturated obstruction
subsumes the earlier masked common-shift family as a special case.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelMaskedSpecialization

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem SeedLiveShiftKernel.liveZeroCoeffSum_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
    (mask : κ → Bool) (s : X) (hs : s ≠ 0) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.liveZeroCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) =
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff := by
  unfold SeedLiveShiftKernel.liveZeroCoeffSum
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hmask : mask i = true
  · simp [hmask, hs]
  · simp [hmask]

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_shiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
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
  have hseed' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i
    simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hseed
  have hshift' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = 0 := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
  simpa [SeedLiveShiftKernel.liveZeroCoeffSum_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
      (X := X) mask s hs seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_liveZeroCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_of_zero_seed_nonzero_shift_witness
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed' hshift' hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_via_shiftKernel
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
  have hseed₁' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₁ +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i
    simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hseed₁
  have hshift₁' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁
          (y₁ +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift₁
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = 0 := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
  have hseed₂' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y₂ +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i
    simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hseed₂
  have hshift₂' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ 0 →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂
          (y₂ +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift₂
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = 0 := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
  exact
    (L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      ⟨t₁, y₁, t₂, y₂, hseed₁', hshift₁', hnz₁, hseed₂', hshift₂', hnz₂, habs⟩)
      ⟨B, hCand⟩

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_shiftKernel_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
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
      (L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_via_shiftKernel
        (ι := ι) (X := X) (κ := κ)
        selector mask s hs seedCoeff liveCoeff a c ν hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x B hCand hseed hshift hnz)

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_via_shiftKernel_of_componentwise_abs_le
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
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁
          (y₁ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity 1
          (y₂ + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂
          (y₂ + s) = 0 ∧
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
      (L.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_via_shiftKernel
        (ι := ι) (X := X) (κ := κ)
        selector mask s seedCoeff liveCoeff a c ν ha hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hwitness)

end WindowedColeHopfHeatSaturatedShiftKernelMaskedSpecialization

end NavierStokes
end FluidDynamics
end Mettapedia
