import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier

/-!
# Seed-Only Operator Obstruction on the Windowed Cole-Hopf Heat Route

This file isolates the first genuinely dynamical obstruction inside the generic
non-pointwise seed/live operator shell on the concrete windowed heat route.

If the descendant operator actually ignores the live slice, then same-route
closure forces the underlying vorticity to be time-invariant at every witness.
So any witness where the concrete route changes in time already rules out such a
literal seed-only bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedOnlyOperatorObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_selfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have h₁ :
      O.operator
          (fun z => T.vorticity 1 z)
          (fun z => T.vorticity t₁ z)
          y =
        T.vorticity t₁ y :=
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself
  have h₂ :
      O.operator
          (fun z => T.vorticity 1 z)
          (fun z => T.vorticity t₂ z)
          y =
        T.vorticity t₂ y :=
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself
  calc
    T.vorticity t₁ y
        = O.operator (fun z => T.vorticity 1 z) (fun z => T.vorticity t₁ z) y := by
          symm
          exact h₁
    _ = O.operator (fun z => T.vorticity 1 z) (fun z => T.vorticity t₂ z) y := by
          exact hseedOnly (fun z => T.vorticity 1 z) (fun z => T.vorticity t₁ z)
            (fun z => T.vorticity t₂ z) y
    _ = T.vorticity t₂ y := h₂

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
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
          (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
            (ι := ι) (X := X)
            selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_selfCompatibility
      (ι := ι) (X := X)
      selector O hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyOperatorTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (hseedOnly : ∀ seed live₁ live₂ y, O.operator seed live₁ y = O.operator seed live₂ y)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t₁ t₂ : NNReal} {y : X}
    (hvary :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
              (ι := ι) (X := X)
              selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedLiveOperatorCandidate
            (ι := ι) (X := X)
            selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector O hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

end WindowedColeHopfHeatSeedOnlyOperatorObstruction

section WindowedColeHopfHeatSeedOnlySampleKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem SeedLiveSampleKernel.toSeedLiveOperator_seedOnly
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0) :
    ∀ seed live₁ live₂ y, K.toSeedLiveOperator.operator seed live₁ y = K.toSeedLiveOperator.operator seed live₂ y := by
  intro seed live₁ live₂ y
  simp [SeedLiveSampleKernel.toSeedLiveOperator, hzero]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
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
          (L.windowedColeHopfHeatSampleKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hseedOnly :
      ∀ seed live₁ live₂ y, K.toSeedLiveOperator.operator seed live₁ y =
        K.toSeedLiveOperator.operator seed live₂ y :=
    K.toSeedLiveOperator_seedOnly hzero
  have hCandOp :
      B.candidate =
        L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector K.toSeedLiveOperator c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa using hCand
  exact
    L.windowedColeHopfHeatSeedOnlyOperator_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X)
      selector K.toSeedLiveOperator hseedOnly c ν hc hν curlFrame curlBound curlBound_nonneg
      hcurl x B hCandOp

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlySampleKernelTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t₁ t₂ : NNReal} {y : X}
    (hvary :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K hzero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

end WindowedColeHopfHeatSeedOnlySampleKernelObstruction

section WindowedColeHopfHeatSeedOnlyShiftKernelObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
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
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (selfCompatibility (Time := NNReal) (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatShiftKernelCandidate
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y : X} :
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y := by
  have hzeroSample : ∀ i, K.toSampleKernel.liveCoeff i = 0 := hzero
  have hCandSample :
      B.candidate =
        L.windowedColeHopfHeatSampleKernelCandidate
          (ι := ι) (X := X)
          selector K.toSampleKernel c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    simpa [WeightedObservable.windowedColeHopfHeatShiftKernelCandidate] using hCand
  exact
    L.windowedColeHopfHeatSeedOnlySampleKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K.toSampleKernel hzeroSample c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCandSample

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ i, K.liveCoeff i = 0)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t₁ t₂ : NNReal} {y : X}
    (hvary :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (selfCompatibility (Time := NNReal) (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatShiftKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hvary <|
    L.windowedColeHopfHeatSeedOnlyShiftKernel_vorticity_eq_of_topDownBridge
      (ι := ι) (X := X) (κ := κ)
      selector K hzero c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

end WindowedColeHopfHeatSeedOnlyShiftKernelObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
