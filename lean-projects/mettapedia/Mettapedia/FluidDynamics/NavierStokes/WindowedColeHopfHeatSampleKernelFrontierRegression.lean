import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier

/-!
# Regression Tests for Windowed Cole-Hopf Sample-Kernel Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSampleKernelFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowedColeHopfHeat_realizes_sampleKernel_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (K : SeedLiveSampleKernel Unit Unit)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := Unit)
        (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector K c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x)) := by
  simpa using
    L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector K c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x

end WindowedColeHopfHeatSampleKernelFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
