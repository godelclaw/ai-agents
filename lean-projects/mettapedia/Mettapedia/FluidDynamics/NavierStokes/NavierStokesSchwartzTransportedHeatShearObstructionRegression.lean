import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzTransportedHeatShearObstruction

/-!
# Navier-Stokes Schwartz transported heat-shear obstruction regression

Focused theorem-level checks for the transported/full-drift heat-shear
Schwartz obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzTransportedHeatShearObstructionRegression

theorem translationInvariantAlong_unit_heatShearTransportFullDrift_streamwise_regression :
    TranslationInvariantAlong heatShearStreamwiseDirection
      (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise 1 1 1 1 1

theorem heatShearTransportInitialVelocity_zero_iff_regression
    (a k b : ℝ) :
    heatShearTransportInitialVelocity a k b = (0 : NSInitialVelocity) ↔
      b = 0 ∧ a * k = 0 := by
  exact heatShearTransportInitialVelocity_eq_zero_iff

theorem not_exists_schwartzInitialVelocity_eq_unit_heatShearTransportInitialVelocity_regression :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearTransportInitialVelocity 1 1 1 := by
  exact
    not_exists_schwartzInitialVelocity_eq_heatShearTransportInitialVelocity_of_transport_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (b := 1) (Or.inl (by norm_num))

theorem not_exists_schwartzInitialVelocity_eq_unit_heatShearTransportFullDriftInitialVelocity_regression :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearTransportFullDriftInitialVelocity 1 1 1 1 1 := by
  exact
    not_exists_schwartzInitialVelocity_eq_heatShearTransportFullDriftInitialVelocity_of_nonzero_transport_or_streamwiseDrift_or_verticalDrift_or_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (Or.inl (by norm_num))

end NavierStokesSchwartzTransportedHeatShearObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
