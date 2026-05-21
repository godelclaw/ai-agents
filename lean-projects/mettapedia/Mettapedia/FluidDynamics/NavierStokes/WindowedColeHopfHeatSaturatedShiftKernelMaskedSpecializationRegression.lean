import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelMaskedSpecialization

/-!
# Regression Tests for Componentwise Saturated Shift-Kernel Masked Specialization
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelMaskedSpecializationRegression

def constantCurlFrame : Fin 2 → Int → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_via_shiftKernel_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 (y₁ + (1 : Int)) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ (y₁ + (1 : Int)) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 (y₂ + (1 : Int)) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ (y₂ + (1 : Int)) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Int)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := Int)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := Fin 2) (X := Int)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := Int) (fun _ : Unit => true) (1 : Int) (fun _ => 0) (fun _ => 1))
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Int)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := Int) (fun _ : Unit => true) (1 : Int) (fun _ => 0) (fun _ => 1)))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := Fin 2) (X := Int)
            selector a c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.not_exists_windowedColeHopfHeatMaskedShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_shifted_witnesses_via_shiftKernel_of_componentwise_abs_le
      (ι := Fin 2) (X := Int) (κ := Unit)
      selector (fun _ : Unit => true) (1 : Int)
      (fun _ => 0) (fun _ => 1)
      a c ν ha hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hwitness

end WindowedColeHopfHeatSaturatedShiftKernelMaskedSpecializationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
