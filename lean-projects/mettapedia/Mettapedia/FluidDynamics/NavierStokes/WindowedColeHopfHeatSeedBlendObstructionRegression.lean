import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendObstruction

/-!
# Regression Tests for Componentwise Seed-Blend Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSeedBlendObstructionRegression

def constantCurlFrame : Fin 2 → Int → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_sum_ne_one_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hnz :
      ∃ y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Int)
            (L.windowedColeHopfHeatSeedBlendInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Int)
              selector 2 0 c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (windowedSelfCompatibility (X := Int))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x),
        B.candidate =
          L.windowedColeHopfHeatSeedBlendCandidate_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector 2 0 c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.not_exists_windowedColeHopfHeatSeedBlendTopDownBridge_of_sum_ne_one_of_nonzero_initial_of_componentwise_abs_le
      (ι := Fin 2) (X := Int)
      selector 2 0 c ν (by norm_num) hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hnz

end WindowedColeHopfHeatSeedBlendObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
