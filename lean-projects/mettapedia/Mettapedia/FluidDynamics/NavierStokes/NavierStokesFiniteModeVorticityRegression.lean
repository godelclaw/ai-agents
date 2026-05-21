import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity

/-!
# Regression Tests for Finite-Mode Vorticity Bounds
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeVorticityRegression

theorem time_independent_schwartz_velocity_uniform_vorticity_bound_regression
    (f : NSSchwartzInitialVelocity) (T : ℝ) :
    uniformVorticityBoundUpTo
      (timeIndependentVelocity (f : NSInitialVelocity)) T
      (schwartzInitialVelocityVorticityBound f) := by
  exact uniformVorticityBoundUpTo_timeIndependentVelocity f T

theorem time_independent_schwartz_velocity_BKM_envelope_regression
    (f : NSSchwartzInitialVelocity) (T : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (timeIndependentVelocity (f : NSInitialVelocity)) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact timeIndependentVelocity_exhibits_BKMEnvelope f T

theorem one_one_two_mode_schwartz_velocity_uniform_vorticity_bound_regression
    (f g : NSSchwartzInitialVelocity) (T : ℝ) :
    uniformVorticityBoundUpTo
      (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) T
      (schwartzInitialVelocityVorticityBound f +
        schwartzInitialVelocityVorticityBound g) := by
  exact uniformVorticityBoundUpTo_oneOneTwoModeSchwartzVelocity f g T

theorem one_one_two_mode_schwartz_velocity_BKM_envelope_regression
    (f g : NSSchwartzInitialVelocity) (T : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
          T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact oneOneTwoModeSchwartzVelocity_exhibits_BKMEnvelope f g T

end NavierStokesFiniteModeVorticityRegression
end NavierStokes
end FluidDynamics
end Mettapedia
