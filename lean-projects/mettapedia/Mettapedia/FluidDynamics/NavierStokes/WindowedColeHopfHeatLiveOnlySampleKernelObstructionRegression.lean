import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatLiveOnlySampleKernelObstruction

/-!
# Regression Tests for Componentwise Live-Only Sample/Shift Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatLiveOnlySampleKernelObstructionRegression

def constantCurlFrame : Fin 2 → Int → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatLiveOnlyShiftKernelTopDownBridge_of_zero_shifted_live_nonzero_live_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ t y,
        (∀ i : Unit,
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t
            (y + (diagonalShiftKernel (X := Int) (1 : Int) 0 1).liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Int)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Int)
              selector
              (diagonalShiftKernel (X := Int) (1 : Int) 0 1)
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
          L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector
            (diagonalShiftKernel (X := Int) (1 : Int) 0 1)
            c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.not_exists_windowedColeHopfHeatLiveOnlyShiftKernelTopDownBridge_of_zero_shifted_live_nonzero_live_of_componentwise_abs_le
      (ι := Fin 2) (X := Int) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Int) (1 : Int) 0 1)
      (by
        intro i
        simp [diagonalShiftKernel])
      c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hwitness

end WindowedColeHopfHeatLiveOnlySampleKernelObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
