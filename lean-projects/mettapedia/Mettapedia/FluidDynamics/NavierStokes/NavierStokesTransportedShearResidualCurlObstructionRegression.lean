import Mettapedia.FluidDynamics.NavierStokes.NavierStokesTransportedShearResidualCurlObstruction

/-!
# Regression tests for transported-shear residual-curl obstructions
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace NavierStokesTransportedShearResidualCurlObstructionRegression

theorem amplitude_transport_shear_heat_ode_mismatch_no_finite_time_witness_regression
    {T : ℝ} (hT : 0 ≤ T) {u₀ : NSInitialVelocity} :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness 1 u₀ T,
      W.velocity = amplitudeShearTransportVelocityField (fun s : NSTime => s + 1) 1 2 := by
  have hA : HasDerivAt (fun s : NSTime => s + 1) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).add_const 1
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
      (A := fun s : NSTime => s + 1) (A' := 1) (ν := 1) (k := 1) (b := 2)
      (T := T) (t := 0) (u₀ := u₀)
      hA (by norm_num) (by norm_num) (by norm_num) hT

theorem amplitude_transport_shear_heat_ode_mismatch_no_bkm_data_regression
    {T : ℝ} (hT : 0 ≤ T) {u₀ : NSInitialVelocity} :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness 1 u₀ T,
      W.velocity = amplitudeShearTransportVelocityField (fun s : NSTime => s + 1) 1 2 ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B := by
  have hA : HasDerivAt (fun s : NSTime => s + 1) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).add_const 1
  exact
    not_exists_BKMData_velocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
      (A := fun s : NSTime => s + 1) (A' := 1) (ν := 1) (k := 1) (b := 2)
      (T := T) (t := 0) (u₀ := u₀)
      hA (by norm_num) (by norm_num) (by norm_num) hT

theorem amplitude_transport_shear_heat_ode_mismatch_no_global_output_velocity_regression
    {u₀ : NSInitialVelocity} :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity 1 u₀
      (amplitudeShearTransportVelocityField (fun s : NSTime => s + 1) 1 2) := by
  have hA : HasDerivAt (fun s : NSTime => s + 1) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).add_const 1
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
      (A := fun s : NSTime => s + 1) (A' := 1) (ν := 1) (k := 1) (b := 2)
      (t := 0) (u₀ := u₀)
      hA (by norm_num) (by norm_num)

end NavierStokesTransportedShearResidualCurlObstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
