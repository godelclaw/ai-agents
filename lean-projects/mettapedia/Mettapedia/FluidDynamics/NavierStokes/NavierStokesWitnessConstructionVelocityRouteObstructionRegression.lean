import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionVelocityRouteObstruction

/-!
# Navier-Stokes Witness-Construction Velocity-Route Obstruction Regression

Small theorem-level checks for the bundled pressure-agnostic witness-
construction route obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionVelocityRouteObstructionRegression

theorem finite_time_witness_failure_blocks_velocity_route_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u) :
    ¬ VelocityWitnessConstructionRoute ν T u₀ u := by
  exact not_VelocityWitnessConstructionRoute_of_not_exists_finiteTimeWitness_velocity hW

theorem velocity_route_classification_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} :
    VelocityWitnessConstructionRoute ν T u₀ u ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u := by
  exact VelocityWitnessConstructionRoute_iff_exists_finiteTimeWitness_velocity

theorem uniform_vorticity_velocity_residual_curl_obstruction_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_uniformVorticityData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      hcurl

theorem velocity_route_residual_curl_obstruction_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ VelocityWitnessConstructionRoute ν T u₀ u := by
  exact not_VelocityWitnessConstructionRoute_of_momentumPressureResidual_vorticity_ne_zero_on hcurl

theorem amplitude_transport_shear_heat_ode_mismatch_no_velocity_route_regression
    {T : ℝ} (hT : 0 ≤ T) {u₀ : NSInitialVelocity} :
    ¬ VelocityWitnessConstructionRoute 1 T u₀
      (amplitudeShearTransportVelocityField (fun s : NSTime => s + 1) 1 2) := by
  have hA : HasDerivAt (fun s : NSTime => s + 1) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).add_const 1
  exact
    not_VelocityWitnessConstructionRoute_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
      (A := fun s : NSTime => s + 1) (A' := 1) (ν := 1) (k := 1) (b := 2)
      (T := T) (t := 0) (u₀ := u₀)
      hA (by norm_num) (by norm_num) (by norm_num) hT

end NavierStokesWitnessConstructionVelocityRouteObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
