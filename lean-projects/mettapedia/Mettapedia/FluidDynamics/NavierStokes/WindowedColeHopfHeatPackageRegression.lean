import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage

/-!
# Regression Tests for Windowed Cole-Hopf Heat Package Componentwise Curl Bounds
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace WindowedColeHopfHeatPackageRegression

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

theorem windowedColeHopfHeat_abs_vorticity_componentwise_constant_regression
    (L : WeightedObservable)
    (selector : Fin 2 → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν constantCurlFrame 2 (by norm_num)
        (by
          intro x i
          norm_num [constantCurlFrame])
        x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := Fin 2) (X := Unit)
        selector c ν hc hν constantCurlFrame 2 (by norm_num)
        (by
          intro x i
          norm_num [constantCurlFrame])
        x).envelope := by
  simpa using
    L.windowedColeHopfHeat_abs_vorticity_le_uniform_of_componentwise_abs_le
      (ι := Fin 2) (X := Unit)
      selector c ν hc hν constantCurlFrame 2 (by norm_num)
      (by
        intro x i
        norm_num [constantCurlFrame])
      x

end WindowedColeHopfHeatPackageRegression
end NavierStokes
end FluidDynamics
end Mettapedia
