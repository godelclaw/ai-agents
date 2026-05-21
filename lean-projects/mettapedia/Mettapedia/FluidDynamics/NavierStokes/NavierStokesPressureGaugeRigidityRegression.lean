import Mettapedia.FluidDynamics.NavierStokes.NavierStokesPressureGaugeRigidity

/-!
# Pressure Gauge Rigidity Regression

Focused regression checks for slab-local and global pressure-gauge rigidity on
the exact witness surfaces.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesPressureGaugeRigidityRegression

theorem same_velocity_exact_witness_pressure_retarget_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    {u : NSVelocityField} {p q : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p)
    (hq : smoothSpaceTimePressure q) :
    (∃ W' : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W'.velocity = u ∧ W'.pressure = q) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient (q - p) t x = 0 := by
  exact
    exists_finiteTimeWitness_with_sameVelocity_pressure_iff_pressureDifference_zeroGradient_on
      hW hq

theorem same_velocity_exact_global_output_pressure_retarget_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p q : NSPressureField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p)
    (hq : smoothSpaceTimePressure q) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u q ↔
      ∀ t x, spatialPressureGradient (q - p) t x = 0 := by
  exact
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_iff_pressureDifference_zeroGradient
      h hq

end NavierStokesPressureGaugeRigidityRegression
end NavierStokes
end FluidDynamics
end Mettapedia
