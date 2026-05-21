import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier

/-!
# Regression Tests for Componentwise Saturated Identity-Sample Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

def liveOnlyIdentitySampleKernel : SeedLiveSampleKernel Unit Unit where
  seedAnchor := fun _ y => y
  liveAnchor := fun _ y => y
  seedCoeff := fun _ => 0
  liveCoeff := fun _ => 1

theorem exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_constant_regression
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
              selector liveOnlyIdentitySampleKernel c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (sampleKernelCompatibilityPred
            (Time := NNReal) (X := Unit) liveOnlyIdentitySampleKernel)
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
  simpa [liveOnlyIdentitySampleKernel] using
    L.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector liveOnlyIdentitySampleKernel 2 1 c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        constructor <;> intro i y <;> cases y <;> simp [liveOnlyIdentitySampleKernel])
      (by
        simp [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
          liveOnlyIdentitySampleKernel]
        norm_num)
      hstat habs

end WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
