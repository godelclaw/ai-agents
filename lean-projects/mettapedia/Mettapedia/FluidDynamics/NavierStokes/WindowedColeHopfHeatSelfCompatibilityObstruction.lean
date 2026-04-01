import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSeededFrontier

/-!
# Self-Compatibility Obstruction for the Windowed Cole-Hopf Heat Route

This file makes the first concrete compatibility obstruction explicit on the
windowed heat route.

The scaled descendant candidate always closes the scaled compatibility mouth,
but it only closes the original self-compatibility mouth in two special cases:

* the scaling factor is `1`; or
* the underlying vorticity tendril is identically zero.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSelfCompatibilityObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_one
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    windowedSelfCompatibility
      (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  simp [WeightedObservable.windowedColeHopfHeatScaledCandidate,
    WeightedObservable.windowedColeHopfHeatCandidate]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hz :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    windowedSelfCompatibility
      (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  simp [WeightedObservable.windowedColeHopfHeatScaledCandidate,
    WeightedObservable.windowedColeHopfHeatCandidate, hz t y]

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    ∀ t y,
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
  intro t y
  have hEq :
      a *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
    simpa [windowedSelfCompatibility,
      WeightedObservable.windowedColeHopfHeatScaledCandidate,
      WeightedObservable.windowedColeHopfHeatCandidate] using hself t y
  have hMul :
      (a - 1) *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
    linarith
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  rcases mul_eq_zero.mp hMul with hzero | hzero
  · exact False.elim (hne hzero)
  · exact hzero

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_eq_one_of_selfCompatibility_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  by_contra ha
  rcases hnz with ⟨t, y, hne⟩
  have hzero :=
    L.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
      (ι := ι) (X := X)
      selector a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  exact hne hzero

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_not_selfCompatibility_of_ne_one_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro hself
  rcases hnz with ⟨t, y, hne⟩
  have hzero :=
    L.windowedColeHopfHeatScaledCandidate_zero_vorticity_of_selfCompatibility_of_ne_one
      (ι := ι) (X := X)
      selector a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x hself t y
  exact hne hzero

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_eq_one_of_topDownBridge_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
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
        (L.windowedColeHopfHeatScaledSeededPredicateKit
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  have hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatScaledCandidate_eq_one_of_selfCompatibility_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatScaledSeededTopDownBridge_of_ne_one_of_nonzero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hnz :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (L.windowedColeHopfHeatScaledSeededPredicateKit
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatScaledCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact ha <|
    L.windowedColeHopfHeatScaledCandidate_eq_one_of_topDownBridge_of_nonzero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz

theorem WeightedObservable.windowedColeHopfHeat_realizes_scaled_seeded_clause_of_one
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_one
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_scaled_seeded_clause_of_zero_vorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hz :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatScaledCandidate_has_selfCompatibility_of_zero_vorticity
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hz)

end WindowedColeHopfHeatSelfCompatibilityObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
