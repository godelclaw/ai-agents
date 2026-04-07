import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier

/-!
# Exactness of the Anchored Spatial Invariant Saturated Corridor

This file proves that the constructive anchored spatial invariant corridor is
already exact.

Under stationarity and invariance under the spatial shift `x ↦ x + s`, if the
anchored spatial blend candidate coincides with the nonlinear saturated
descendant and the total coefficient sum is nonzero, then all nonzero witness
magnitudes must agree.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
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
  let coeffSum := baseCoeff + seedCoeff + shiftCoeff
  have hEqPoint (t : NNReal) (y : X) :
      satCoeff * (T.vorticity t y / (1 + |T.vorticity t y|)) = coeffSum * T.vorticity t y := by
    calc
      satCoeff * (T.vorticity t y / (1 + |T.vorticity t y|))
          = (L.windowedColeHopfHeatSaturatedCandidate
              (ι := ι) (X := X)
              selector satCoeff c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                rfl
      _ = (L.windowedColeHopfHeatAnchoredShiftCandidate
              (ι := ι) (X := X)
              selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                exact congrFun (congrFun (congrArg VelocityPressureCandidate.velocity hCand.symm) t) y
      _ = coeffSum * T.vorticity t y := by
            simp [coeffSum, T, WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate,
              UniformVorticityTendril.seedLiveOperatorCandidate, anchoredSeedLiveBlendOperator,
              hshiftInv t y, hstat t (y + s), add_assoc, add_left_comm, add_comm, add_mul]
  have hCoeffFormula (t : NNReal) (y : X) (hnz : T.vorticity t y ≠ 0) :
      coeffSum * (1 + |T.vorticity t y|) = satCoeff := by
    let w := T.vorticity t y
    have hw : satCoeff * (w / (1 + |w|)) = coeffSum * w := by
      simpa [w] using hEqPoint t y
    have hden : (1 + |w|) ≠ 0 := by positivity
    have hmul : satCoeff * w = (coeffSum * (1 + |w|)) * w := by
      calc
        satCoeff * w = (satCoeff * (w / (1 + |w|))) * (1 + |w|) := by
          field_simp [hden]
        _ = (coeffSum * w) * (1 + |w|) := by
          rw [hw]
        _ = (coeffSum * (1 + |w|)) * w := by
          ring
    have hzero : (satCoeff - coeffSum * (1 + |w|)) * w = 0 := by
      nlinarith [hmul]
    rcases mul_eq_zero.mp hzero with hfac | hwzero
    · linarith
    · exact False.elim (hnz hwzero)
  have h1 : coeffSum * (1 + |T.vorticity t₁ y₁|) = satCoeff :=
    hCoeffFormula t₁ y₁ hnz₁
  have h2 : coeffSum * (1 + |T.vorticity t₂ y₂|) = satCoeff :=
    hCoeffFormula t₂ y₂ hnz₂
  have hdiff :
      coeffSum *
        (|T.vorticity t₁ y₁| - |T.vorticity t₂ y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hdiff with hsum0 | habs
  · exact False.elim (hsum (by simpa [coeffSum] using hsum0))
  · linarith

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hCand
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz₁ hnz₂
  exact habs hEq

end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
