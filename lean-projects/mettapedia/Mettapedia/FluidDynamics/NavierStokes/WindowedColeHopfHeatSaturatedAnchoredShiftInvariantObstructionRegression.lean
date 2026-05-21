import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

/-!
# Regression Tests for Componentwise Saturated Anchored Shift-Invariant Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_componentwise_constant_regression
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
    (habs :
      ∀ t : NNReal, ∀ y : Unit,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t y| = 1) :
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
  have hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity 1 () ≠ 0 := by
    have habs1 := habs 1 ()
    intro hz
    simp [hz] at habs1
  exact
    L.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 1 c ν
      (by norm_num)
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
      hnz

theorem not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_componentwise_constant_regression
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
    (habs :
      ∀ t : NNReal, ∀ y : Unit,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t y| = 1) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Unit)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector (anchoredTranslationShiftKernel (X := Unit) () 1 0 0)
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (anchoredTranslationShiftKernel (X := Unit) () 1 0 0))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector 1 c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  have hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity 1 () ≠ 0 := by
    have habs1 := habs 1 ()
    intro hz
    simp [hz] at habs1
  exact
    L.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 1 c ν
      (by norm_num)
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
      hnz

end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
