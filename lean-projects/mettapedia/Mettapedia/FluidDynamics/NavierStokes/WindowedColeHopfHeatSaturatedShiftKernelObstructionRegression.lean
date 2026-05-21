import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelObstruction

/-!
# Regression Tests for Componentwise Saturated Shift-Kernel Obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatSaturatedShiftKernelObstructionRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (∀ i : Unit,
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₁ + (diagonalShiftKernel (X := Unit) () 1 0).seedShift i) = 0) ∧
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₁ (y₁ + (diagonalShiftKernel (X := Unit) () 1 0).liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ y₁ ≠ 0 ∧
        (∀ i : Unit,
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₂ + (diagonalShiftKernel (X := Unit) () 1 0).seedShift i) = 0) ∧
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity t₂ (y₂ + (diagonalShiftKernel (X := Unit) () 1 0).liveShift i) = 0) ∧
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
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_seed_nonzero_shift_witnesses_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 1 0)
      a c ν ha hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hwitness

theorem not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_other_anchors_nonzero_initials_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (a c ν : ℝ)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ y₁ y₂,
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₁ + (diagonalShiftKernel (X := Unit) () 1 0).seedShift i) = 0) ∧
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₁ + (diagonalShiftKernel (X := Unit) () 1 0).liveShift i) = 0) ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y₁ ≠ 0 ∧
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).seedShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₂ + (diagonalShiftKernel (X := Unit) () 1 0).seedShift i) = 0) ∧
        (∀ i : Unit, (diagonalShiftKernel (X := Unit) () 1 0).liveShift i ≠ 0 →
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := Fin 2) (X := Unit)
            selector c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x).vorticity 1 (y₂ + (diagonalShiftKernel (X := Unit) () 1 0).liveShift i) = 0) ∧
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
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_with_zero_other_anchors_nonzero_initials_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit) (κ := Unit)
      selector
      (diagonalShiftKernel (X := Unit) () 1 0)
      a c ν ha hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hwitness

theorem not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (satCoeff c ν : ℝ)
    (hsat : satCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState)
    (hwitness :
      ∃ t₁ y₁ t₂ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 y₁ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 (y₁ + ()) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₁ (y₁ + ()) = 0 ∧
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
          x).vorticity 1 y₂ = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity 1 (y₂ + ()) = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := Fin 2) (X := Unit)
          selector c ν hc hν
          constantCurlFrame 2 (by norm_num)
          (by
            intro y i
            norm_num [constantCurlFrame])
          x).vorticity t₂ (y₂ + ()) = 0 ∧
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
              selector (anchoredTranslationShiftKernel (X := Unit) () 1 0 0)
              c ν hc hν
              constantCurlFrame 2 (by norm_num)
              (by
                intro y i
                norm_num [constantCurlFrame])
              x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := Unit)
            (anchoredTranslationShiftKernel (X := Unit) () 1 0 0))
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
            selector satCoeff c ν hc hν
            constantCurlFrame 2 (by norm_num)
            (by
              intro y i
              norm_num [constantCurlFrame])
            x := by
  simpa using
    L.not_exists_windowedColeHopfHeatAnchoredTranslationShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector () 1 0 0 satCoeff c ν hsat hc hν
      constantCurlFrame 2 (by norm_num)
      (by
        intro y i
        norm_num [constantCurlFrame])
      x hwitness

end WindowedColeHopfHeatSaturatedShiftKernelObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
