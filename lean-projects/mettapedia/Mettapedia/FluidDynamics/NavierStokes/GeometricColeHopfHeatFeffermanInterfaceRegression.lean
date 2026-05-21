import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfHeatFeffermanInterface

/-!
# Regression Tests for Componentwise Curl Bounds in the Geometric Heat Fefferman Interface
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace GeometricColeHopfHeatFeffermanInterfaceRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem geometricColeHopfHeat_abs_vorticity_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    ∀ t y,
      |(L.geometricColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector ν B hν hB cutoff hcutoff_cont hcutoff
        constantCurlFrame 2 (by norm_num)
        (by
          intro x i
          norm_num [constantCurlFrame])
        x).vorticity t y| ≤
      L.geometricColeHopfHeatEnvelope (ι := Fin 2) ν B ((Fintype.card (Fin 2) : ℝ) * 2 ^ 2) := by
  simpa using
    L.geometricColeHopfHeat_abs_vorticity_le_uniform_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      constantCurlFrame 2 (by norm_num)
      (by
        intro x i
        norm_num [constantCurlFrame])
      x

end GeometricColeHopfHeatFeffermanInterfaceRegression
end NavierStokes
end FluidDynamics
end Mettapedia
