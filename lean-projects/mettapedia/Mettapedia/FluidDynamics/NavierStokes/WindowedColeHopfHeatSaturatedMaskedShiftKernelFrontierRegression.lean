import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontier

/-!
# Regression Tests for Componentwise Saturated Masked Shift-Kernel Frontier
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontierRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem exists_windowedColeHopfHeatSaturatedMaskedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_constant_regression
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
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Unit)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := Unit) (fun _ : Unit => true) () (fun _ => 0) (fun _ => 1))
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := Unit) (fun _ : Unit => true) () (fun _ => 0) (fun _ => 1)))
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
    L.exists_windowedColeHopfHeatSaturatedMaskedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector (fun _ : Unit => true) () (fun _ => 0) (fun _ => 1)
      2 1 c ν hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
          SeedLiveShiftKernel.liveCoeffSum,
          SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel]
        norm_num)
      (by
        intro t y
        cases y
        simp)
      hstat habs

end WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontierRegression
end NavierStokes
end FluidDynamics
end Mettapedia
