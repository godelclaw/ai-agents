import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontier

/-!
# Regression Tests for Componentwise Saturated Diagonal Sample-Kernel Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem exists_windowedColeHopfHeatSaturatedDiagonalSampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_constant_regression
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
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Unit)
            (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector (diagonalSampleKernel (X := Unit) 1 0) c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (sampleKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (diagonalSampleKernel (X := Unit) 1 0))
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
            selector 2 c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.exists_windowedColeHopfHeatSaturatedDiagonalSampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector 1 0 2 1 c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by norm_num)
      hstat habs

end WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
