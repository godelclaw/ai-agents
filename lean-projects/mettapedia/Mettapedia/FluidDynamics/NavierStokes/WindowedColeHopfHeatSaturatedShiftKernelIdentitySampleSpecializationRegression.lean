import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelIdentitySampleSpecialization

/-!
# Regression Tests for Componentwise Saturated Shift-Kernel Identity-Sample Specialization
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelIdentitySampleSpecializationRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

def liveOnlyIdentitySampleKernel : SeedLiveSampleKernel Unit Unit where
  seedAnchor := fun _ y => y
  liveAnchor := fun _ y => y
  seedCoeff := fun _ => 0
  liveCoeff := fun _ => 1

theorem not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_via_saturatedShiftKernel_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 y₂|) :
    ¬ ∃ B :
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
            selector a c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa [liveOnlyIdentitySampleKernel] using
    L.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_via_saturatedShiftKernel_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector liveOnlyIdentitySampleKernel a c ν ha hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x
      (by
        constructor <;> intro i y <;> cases y <;> simp [liveOnlyIdentitySampleKernel])
      hwitness

end WindowedColeHopfHeatSaturatedShiftKernelIdentitySampleSpecializationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
