import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelObstruction

/-!
# Same-Route Obstruction for a Finite Masked Shift-Kernel Family

This file widens the first concrete spatial same-route obstruction from one
anchored descendant to a finite family. The family keeps a common seed shift
`s`, while each live term either stays at `x` or moves to `x + s` according to
a Boolean mask.

So the family still collapses to the three-coefficient anchored spatial route,
and the same witness-based rigidity laws survive at that finite-family level.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatMaskedShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

namespace SeedLiveShiftKernel

def maskedSeedCoeffSum (seedCoeff : κ → ℝ) : ℝ :=
  ∑ i, seedCoeff i

def maskedLiveBaseCoeffSum (mask : κ → Bool) (liveCoeff : κ → ℝ) : ℝ :=
  ∑ i, if mask i then 0 else liveCoeff i

def maskedLiveShiftCoeffSum (mask : κ → Bool) (liveCoeff : κ → ℝ) : ℝ :=
  ∑ i, if mask i then liveCoeff i else 0

/-- Finite family with one common seed shift and a Boolean choice between live
staying at `x` or moving to `x + s`. -/
def maskedAnchoredTranslationShiftKernel
    (mask : κ → Bool) (s : X)
    (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel κ X where
  seedShift := fun _ => s
  liveShift := fun i => if mask i then s else 0
  seedCoeff := seedCoeff
  liveCoeff := liveCoeff

end SeedLiveShiftKernel

theorem WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_eq_anchoredShiftCandidate_of_maskedAnchoredTranslation
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
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s
      (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
      (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
      (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  unfold WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate
  congr
  funext t y
  have hseed :
      (∑ i, seedCoeff i * T.vorticity 1 (y + s)) =
        T.vorticity 1 (y + s) * ∑ i, seedCoeff i := by
    simpa [mul_comm] using
      (Finset.sum_mul (s := Finset.univ)
        (f := fun i : κ => seedCoeff i)
        (a := T.vorticity 1 (y + s))).symm
  have hlive :
      (∑ i, liveCoeff i * T.vorticity t (y + if mask i = true then s else 0)) =
        (∑ i, if mask i = true then liveCoeff i else 0) * T.vorticity t (y + s) +
        (∑ i, if mask i = true then 0 else liveCoeff i) * T.vorticity t y := by
    calc
      (∑ i, liveCoeff i * T.vorticity t (y + if mask i = true then s else 0))
          = ∑ i,
              ((if mask i = true then liveCoeff i else 0) * T.vorticity t (y + s) +
                (if mask i = true then 0 else liveCoeff i) * T.vorticity t y) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h : mask i = true
              · simp [h]
              · simp [h]
      _ = (∑ i, if mask i = true then liveCoeff i else 0) * T.vorticity t (y + s) +
            (∑ i, if mask i = true then 0 else liveCoeff i) * T.vorticity t y := by
            rw [Finset.sum_add_distrib]
            rw [(Finset.sum_mul (s := Finset.univ)
                  (f := fun i : κ => if mask i = true then liveCoeff i else 0)
                  (a := T.vorticity t (y + s))).symm]
            rw [(Finset.sum_mul (s := Finset.univ)
                  (f := fun i : κ => if mask i = true then 0 else liveCoeff i)
                  (a := T.vorticity t y)).symm]
  simp [SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel,
    SeedLiveShiftKernel.maskedSeedCoeffSum, SeedLiveShiftKernel.maskedLiveBaseCoeffSum,
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum, anchoredSeedLiveBlendOperator]
  rw [Finset.sum_add_distrib, hseed, hlive]
  ring

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff = 1 := by
  have hselfShift :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfAnchored :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s
          (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
          (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
          (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatShiftKernelCandidate_eq_anchoredShiftCandidate_of_maskedAnchoredTranslation
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x] using hselfShift
  exact
    L.windowedColeHopfHeatAnchoredShift_a_eq_one_of_selfCompatibility_of_zero_shifted_initial_zero_shifted_live_nonzero_live
      (ι := ι) (X := X)
      selector s
      (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
      (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
      (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfAnchored hwitness

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_live_nonzero_shifted_initial
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
  have hselfShift :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfAnchored :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s
          (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
          (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
          (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatShiftKernelCandidate_eq_anchoredShiftCandidate_of_maskedAnchoredTranslation
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x] using hselfShift
  exact
    L.windowedColeHopfHeatAnchoredShift_b_eq_zero_of_selfCompatibility_of_zero_live_zero_shifted_live_nonzero_shifted_initial
      (ι := ι) (X := X)
      selector s
      (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
      (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
      (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfAnchored hwitness

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_initial_nonzero_shifted_live
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 (y + s) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) ≠ 0) :
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff = 0 := by
  have hselfShift :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector
          (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
            (X := X) mask s seedCoeff liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  have hselfAnchored :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s
          (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
          (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
          (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
          c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [L.windowedColeHopfHeatShiftKernelCandidate_eq_anchoredShiftCandidate_of_maskedAnchoredTranslation
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x] using hselfShift
  exact
    L.windowedColeHopfHeatAnchoredShift_d_eq_zero_of_selfCompatibility_of_zero_live_zero_shifted_initial_nonzero_shifted_live
      (ι := ι) (X := X)
      selector s
      (SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff)
      (SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff)
      (SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hselfAnchored hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveBaseCoeffSum_ne_one_of_zero_shifted_initial_zero_shifted_live_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (ha :
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff ≠ 1)
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
  exact ha <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveBaseCoeffSum_eq_one_of_topDownBridge_of_zero_shifted_initial_zero_shifted_live_nonzero_live
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_seedCoeffSum_ne_zero_of_zero_live_zero_shifted_live_nonzero_shifted_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hb :
      SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff ≠ 0)
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
  exact hb <|
    L.windowedColeHopfHeatMaskedShiftKernel_seedCoeffSum_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_live_nonzero_shifted_initial
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_of_liveShiftCoeffSum_ne_zero_of_zero_live_zero_shifted_initial_nonzero_shifted_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (c ν : ℝ)
    (hd :
      SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff ≠ 0)
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
  exact hd <|
    L.windowedColeHopfHeatMaskedShiftKernel_liveShiftCoeffSum_eq_zero_of_topDownBridge_of_zero_live_zero_shifted_initial_nonzero_shifted_live
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

end WindowedColeHopfHeatMaskedShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
