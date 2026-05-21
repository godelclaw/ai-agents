import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedOnlyOperatorObstruction

/-!
# Regression Tests for Componentwise Seed-Only Operator Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSeedOnlyOperatorObstructionRegression

def constantCurlFrame : Fin 2 → Int → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hvary :
      ∃ t₁ t₂ y,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ y ≠
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ y) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Int)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Int)
              selector
              (diagonalShiftKernel (X := Int) (1 : Int) 1 0)
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
            (diagonalShiftKernel (X := Int) (1 : Int) 1 0)
            c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  rcases hvary with ⟨t₁, t₂, y, hvary⟩
  simpa using
    L.not_exists_windowedColeHopfHeatSeedOnlyShiftKernelTopDownBridge_of_vorticity_ne_of_componentwise_abs_le
      (ι := Fin 2) (X := Int) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Int) (1 : Int) 1 0)
      (by
        intro i
        simp [diagonalShiftKernel])
      c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hvary

end WindowedColeHopfHeatSeedOnlyOperatorObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
