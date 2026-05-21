import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzHeatShearObstruction

/-!
# Navier-Stokes Schwartz heat-shear obstruction regression

Focused theorem-level checks for the concrete Schwartz obstruction on the
heat-shear initial datum.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzHeatShearObstructionRegression

theorem heatShearStreamwiseDirection_ne_zero_regression :
    heatShearStreamwiseDirection ≠ 0 := by
  exact heatShearStreamwiseDirection_ne_zero

theorem translationInvariantAlong_heatShearInitialVelocity_streamwise_regression
    (a k : ℝ) :
    TranslationInvariantAlong heatShearStreamwiseDirection
      (heatShearInitialVelocity a k) := by
  exact translationInvariantAlong_heatShearInitialVelocity_streamwise a k

theorem heatShearInitialVelocity_unit_ne_zero_regression :
    heatShearInitialVelocity 1 1 ≠ (0 : NSInitialVelocity) := by
  exact
    heatShearInitialVelocity_ne_zero_of_amplitude_ne_zero_of_wavenumber_ne_zero
      (a := 1) (k := 1) (by norm_num) (by norm_num)

theorem not_exists_schwartzInitialVelocity_eq_unit_heatShearInitialVelocity_regression :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearInitialVelocity 1 1 := by
  exact
    not_exists_schwartzInitialVelocity_eq_heatShearInitialVelocity_of_amplitude_ne_zero_of_wavenumber_ne_zero
      (a := 1) (k := 1) (by norm_num) (by norm_num)

end NavierStokesSchwartzHeatShearObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
