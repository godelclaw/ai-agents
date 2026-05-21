import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier

/-!
# Regression Tests for Componentwise Windowed Cole-Hopf Heat Shift-Kernel Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatShiftKernelFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowedColeHopfHeat_realizes_shiftKernel_clause_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := Unit)
        (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit) (κ := Unit)
          selector
          (diagonalShiftKernel (X := Unit) () 1 0)
          c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro x i
            norm_num [constantCurlFrame])
          x)) := by
  simpa using
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 1 0)
      c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro x i
        norm_num [constantCurlFrame])
      x

end WindowedColeHopfHeatShiftKernelFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
