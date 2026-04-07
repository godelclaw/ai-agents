import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatMaskedShiftKernelObstruction

/-!
# Masked Common-Shift Specialization of the General Linear Shift-Kernel Obstruction

This file shows that the newer generic linear finite shift-kernel shell
subsumes the older masked common-shift shell.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelMaskedSpecialization

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem SeedLiveShiftKernel.seedCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedSeedCoeffSum
    (mask : κ → Bool) (s : X) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.seedCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) s =
      SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff := by
  unfold SeedLiveShiftKernel.seedCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedSeedCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

theorem SeedLiveShiftKernel.liveCoeffSumAt_zero_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
    (mask : κ → Bool) (s : X) (hs : s ≠ 0) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.liveCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) 0 =
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff := by
  unfold SeedLiveShiftKernel.liveCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hmask : mask i = true
  · simp [hmask, hs]
  · simp [hmask]

theorem SeedLiveShiftKernel.liveCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedLiveShiftCoeffSum
    (mask : κ → Bool) (s : X) (hs : s ≠ 0) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.liveCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) s =
      SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff := by
  have hzero : ¬ (0 = s) := by
    intro h
    exact hs h.symm
  unfold SeedLiveShiftKernel.liveCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hmask : mask i = true
  · simp [hmask]
  · simp [hmask, hzero]

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff = 1 := by
  rcases hwitness with ⟨t, y, hseed, hshift, hnz⟩
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
  have hlive' :
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
  simpa [SeedLiveShiftKernel.liveCoeffSumAt_zero_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
      (X := X) mask s hs seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_zero_eq_one_of_topDownBridge_of_zero_seed_other_live_zero_witness
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hseed' hlive' hnz

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) ≠ 0) :
    SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff = 0 := by
  rcases hwitness with ⟨t, y, hzero, hshift, hseedNz⟩
  have hlive' :
      ∀ i : κ,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i
    by_cases hmask : mask i = true
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshift
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hzero
  have hseedOther' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).seedShift i ≠ s →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).seedShift i) = 0 := by
    intro i hi
    have : ¬ ((SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).seedShift i ≠ s) := by
      simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel]
    exact False.elim (this hi)
  simpa [SeedLiveShiftKernel.seedCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedSeedCoeffSum
      (X := X) mask s seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_seedCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_other_seed_nonzero_seed
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      s c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hlive' hseedOther' hseedNz

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
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
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) ≠ 0) :
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff = 0 := by
  rcases hwitness with ⟨t, y, hzero, hseed, hliveNz⟩
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
  have hliveOther' :
      ∀ i : κ,
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i ≠ s →
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y +
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff).liveShift i) = 0 := by
    intro i hi
    by_cases hmask : mask i = true
    · have : (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff).liveShift i = s := by
        simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask]
      exact False.elim (hi this)
    · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hzero
  simpa [SeedLiveShiftKernel.liveCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedLiveShiftCoeffSum
      (X := X) mask s hs seedCoeff liveCoeff] using
    L.windowedColeHopfHeatShiftKernel_liveCoeffSumAt_eq_zero_of_topDownBridge_of_zero_live_zero_seed_zero_other_live_nonzero_live
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      s c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      B hCand hzero hseed' hliveOther' hliveNz

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveBaseCoeffSum_ne_one_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hbase : SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
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
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hbase <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s hs seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_seedCoeffSum_ne_zero_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hseedMass : SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) ≠ 0) :
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
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hseedMass <|
    L.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveShiftCoeffSum_ne_zero_via_generalShiftKernel
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (hs : s ≠ 0)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hliveMass : SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) ≠ 0) :
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
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hliveMass <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_via_generalShiftKernel
      (ι := ι) (X := X)
      selector mask s hs seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

end WindowedColeHopfHeatGeneralShiftKernelMaskedSpecialization

end NavierStokes
end FluidDynamics
end Mettapedia
