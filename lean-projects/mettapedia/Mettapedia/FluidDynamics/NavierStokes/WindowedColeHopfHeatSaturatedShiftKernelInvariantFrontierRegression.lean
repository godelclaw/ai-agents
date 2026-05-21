import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

/-!
# Regression Tests for Componentwise Saturated Shift-Kernel Invariant Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowedColeHopfHeat_realizes_saturated_shiftKernel_invariant_clause_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (habs :
      ∀ t : NNReal, ∀ y : Unit,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := Unit)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector 0 c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x)) := by
  simpa using
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 0 0)
      0 r c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
          SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel])
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      habs

theorem exists_windowedColeHopfHeat_saturated_shiftKernel_invariant_bridge_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (r c ν : ℝ)
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
            x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Unit)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector (diagonalShiftKernel (X := Unit) () 0 0)
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (diagonalShiftKernel (X := Unit) () 0 0))
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
            selector 0 c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 0 0)
      0 r c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
          SeedLiveShiftKernel.liveCoeffSum, diagonalShiftKernel])
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      (by
        intro i t y
        cases y
        simp [diagonalShiftKernel])
      hstat habs

end WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
