import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorObstruction

/-!
# Regression Tests for Componentwise Seed/Live Operator Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSeedLiveOperatorObstructionRegression

def constantCurlFrame : Fin 2 → Int → ℝ := fun _ _ => 2

abbrev seedOnlyDiagonalOperator : SeedLiveOperator Int :=
  (diagonalSampleKernel (X := Int) 0 1).toSeedLiveOperator

theorem not_exists_windowedColeHopfHeatSeedLiveOperatorTopDownBridge_of_diagonalSampleKernel_seed_route_operator_ne_live_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hvary :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y ≠
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Int)
            (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Int)
              selector
              seedOnlyDiagonalOperator
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (selfCompatibility (Time := NNReal) (X := Int))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x),
        B.candidate =
          L.windowedColeHopfHeatSeedLiveOperatorCandidate_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector
            seedOnlyDiagonalOperator
            c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  rcases hvary with ⟨t, y, hvary⟩
  have hop :
      seedOnlyDiagonalOperator.operator
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 z)
        (fun z =>
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t z)
        y ≠
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Int)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t y := by
    simpa [seedOnlyDiagonalOperator, SeedLiveSampleKernel.toSeedLiveOperator, diagonalSampleKernel]
      using hvary
  exact
    L.not_exists_windowedColeHopfHeatSeedLiveOperatorTopDownBridge_of_operator_ne_live_of_componentwise_abs_le
      (ι := Fin 2) (X := Int)
      selector
      seedOnlyDiagonalOperator
      c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hop

end WindowedColeHopfHeatSeedLiveOperatorObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
