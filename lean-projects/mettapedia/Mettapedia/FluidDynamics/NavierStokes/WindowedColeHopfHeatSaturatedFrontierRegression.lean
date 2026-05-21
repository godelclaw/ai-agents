import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Regression Tests for Componentwise Saturated Windowed Cole-Hopf Heat Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowedColeHopfHeat_realizes_saturated_clause_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := Unit)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector a c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro x i
            norm_num [constantCurlFrame])
          x)) := by
  simpa using
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector a c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro x i
        norm_num [constantCurlFrame])
      x

end WindowedColeHopfHeatSaturatedFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
