import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorFrontier

/-!
# Generic Seed/Live Operator Obstruction on the Windowed Cole-Hopf Heat Route

This file isolates the shared same-route obstruction for every non-pointwise
seed/live operator descendant on the concrete windowed heat route.

If a literal same-route bridge exists for an operator descendant, then the
operator output itself must agree with the live vorticity at every witness.  So
any witness where the operator disagrees already rules out that literal bridge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedLiveOperatorObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
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
    {t : NNReal} {y : X} :
    O.operator
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 z)
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t z)
        y =
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
  simpa [selfCompatibility, WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate] using
    hself t y

theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperator_eq_live_of_topDownBridge
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
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
    {t : NNReal} {y : X} :
    O.operator
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 z)
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t z)
        y =
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
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
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_selfCompatibility
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedLiveOperatorTopDownBridge_of_operator_ne_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    {t : NNReal} {y : X}
    (hop :
      O.operator
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 z)
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t z)
        y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
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
  exact hop <|
    L.windowedColeHopfHeatSeedLiveOperator_eq_live_of_topDownBridge
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand

end WindowedColeHopfHeatSeedLiveOperatorObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
