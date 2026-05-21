import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantAnchoredSpecialization

/-!
# Regression Tests for Componentwise Anchored Specialization of the Invariant Saturated Shift-Kernel Exactness Theorem
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelInvariantAnchoredSpecializationRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowed_heat_saturated_invariantAnchored_abs_eq_abs_via_shiftKernelInvariant_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hstat :
      ∀ t : NNReal, ∀ y : Unit,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector () 1 0 0 c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x =
      L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector 1 c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x)
    {t₁ t₂ : NNReal}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t₁ () ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t₂ () ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t₁ ()| =
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t₂ ()| := by
  simpa using
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_via_shiftKernelInvariant_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 1 c ν
      (by norm_num)
      hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        intro t y
        cases y
        simp)
      hstat hCand hnz₁ hnz₂

theorem not_windowed_heat_saturated_invariantAnchored_candidate_eq_via_shiftKernelInvariant_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hstat :
      ∀ t : NNReal, ∀ y : Unit,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t y)
    (hwitness :
      ∃ t₁ t₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ () ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ () ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₁ ()| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₂ ()|) :
    L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x ≠
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector 1 c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x := by
  rcases hwitness with ⟨t₁, t₂, hnz₁, hnz₂, habs⟩
  exact
    L.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_via_shiftKernelInvariant_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 1 c ν
      (by norm_num)
      hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        intro t y
        cases y
        simp)
      hstat
      ⟨t₁, t₂, (), (), hnz₁, hnz₂, habs⟩

end WindowedColeHopfHeatSaturatedShiftKernelInvariantAnchoredSpecializationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
