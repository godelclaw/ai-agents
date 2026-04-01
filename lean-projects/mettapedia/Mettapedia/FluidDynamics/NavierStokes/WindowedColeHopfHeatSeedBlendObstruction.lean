import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendFrontier

/-!
# Same-Route Obstruction for the Windowed Seed-Blend Frontier

This file records the first concrete same-route rigidity laws for the affine
seed-blend candidate

`u(t,x) = a * ω(t,x) + b * ω(1,x)`.

The main theme is that original self-compatibility forces sharp algebraic
constraints on `(a,b)` whenever the concrete vorticity field is not degenerate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedBlendObstruction

variable {ι X : Type*}
variable [Fintype ι]

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_sum_eq_one_of_selfCompatibility_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    a + b = 1 := by
  rcases hnz with ⟨y, hne⟩
  have hEq :
      a *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y +
        b *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y := by
    simpa [windowedSelfCompatibility, WeightedObservable.windowedColeHopfHeatSeedBlendCandidate] using
      hself 1 y
  have hMul :
      (a + b - 1) *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 := by
    linarith
  rcases mul_eq_zero.mp hMul with hzero | hzero
  · linarith
  · exact False.elim (hne hzero)

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_a_eq_one_of_selfCompatibility_of_zero_initial_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    a = 1 := by
  rcases hwitness with ⟨t, y, hzero, hne⟩
  have hEq :
      a *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y +
        b *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
    simpa [windowedSelfCompatibility, WeightedObservable.windowedColeHopfHeatSeedBlendCandidate] using
      hself t y
  have hMul :
      (a - 1) *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 := by
    rw [hzero] at hEq
    linarith
  rcases mul_eq_zero.mp hMul with hfactor | hv
  · linarith
  · exact False.elim (hne hv)

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_b_eq_zero_of_selfCompatibility_of_zero_live_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    b = 0 := by
  rcases hwitness with ⟨t, y, hzero, hne⟩
  have hEq :
      a *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y +
        b *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
    simpa [windowedSelfCompatibility, WeightedObservable.windowedColeHopfHeatSeedBlendCandidate] using
      hself t y
  have hMul :
      b *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 := by
    rw [hzero] at hEq
    linarith
  rcases mul_eq_zero.mp hMul with hb | hv
  · exact hb
  · exact False.elim (hne hv)

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_sum_eq_one_of_topDownBridge_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    a + b = 1 := by
  have hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatSeedBlend_sum_eq_one_of_selfCompatibility_of_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hnz

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_sum_ne_one_of_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hab : a + b ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice
              (ι := ι) (X := X)
              selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hab <|
    L.windowedColeHopfHeatSeedBlend_sum_eq_one_of_topDownBridge_of_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hnz

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_a_eq_one_of_topDownBridge_of_zero_initial_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 ∧
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
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatSeedBlend_a_eq_one_of_selfCompatibility_of_zero_initial_nonzero_live
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hwitness

theorem WeightedObservable.windowedColeHopfHeatSeedBlend_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
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
          (L.windowedColeHopfHeatSeedBlendInitialSlice
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (windowedSelfCompatibility (X := X))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    b = 0 := by
  have hself :
      windowedSelfCompatibility
        (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedBlendCandidate
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  exact
    L.windowedColeHopfHeatSeedBlend_b_eq_zero_of_selfCompatibility_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_one_of_zero_initial_nonzero_live
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (ha : a ≠ 1)
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice
              (ι := ι) (X := X)
              selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact ha <|
    L.windowedColeHopfHeatSeedBlend_a_eq_one_of_topDownBridge_of_zero_initial_nonzero_live
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

theorem WeightedObservable.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_ne_zero_of_zero_live_nonzero_initial
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hb : b ≠ 0)
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
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSeedBlendInitialSlice
              (ι := ι) (X := X)
              selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate
            (ι := ι) (X := X)
            selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  exact hb <|
    L.windowedColeHopfHeatSeedBlend_b_eq_zero_of_topDownBridge_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x B hCand hwitness

end WindowedColeHopfHeatSeedBlendObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
