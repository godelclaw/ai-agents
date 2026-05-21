import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction

/-!
# Regression Tests for Componentwise Saturated Shift-Kernel Invariant Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelInvariantObstructionRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
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
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Unit)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector (diagonalShiftKernel (X := Unit) () 1 0)
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (diagonalShiftKernel (X := Unit) () 1 0))
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
            selector a c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 1 0)
      a c ν
      (by
        simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
          SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel])
      hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      hstat hwitness

theorem not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_totalCoeffSum_of_componentwise_constant_regression
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
    {t : NNReal} {y : Unit}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Unit)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector (diagonalShiftKernel (X := Unit) () 1 0)
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (diagonalShiftKernel (X := Unit) () 1 0))
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
  simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel]
    using
      L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_totalCoeffSum_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit) (κ := Unit)
        selector
        (diagonalShiftKernel (X := Unit) () 1 0)
        1 c ν
        (by
          simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
            SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel])
        (by
          simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
            SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel])
        hc hν
        constantCurlFrame 2 (by norm_num)
        (by
          intro y i
          norm_num [constantCurlFrame])
        x
        (by
          intro i t y
          cases y
          simp [diagonalShiftKernel])
        (by
          intro i t y
          cases y
          simp [diagonalShiftKernel])
        hstat hnz

end WindowedColeHopfHeatSaturatedShiftKernelInvariantObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
