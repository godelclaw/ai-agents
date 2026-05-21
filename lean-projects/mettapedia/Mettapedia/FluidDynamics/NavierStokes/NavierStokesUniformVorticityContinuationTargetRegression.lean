import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Navier-Stokes Uniform Vorticity Continuation Target Regression

Small theorem-level checks for the generic whole-space energy obstructions on
the continuation target surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesUniformVorticityContinuationTargetRegression

theorem finite_time_witness_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT

theorem finite_time_witness_velocity_eq_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hWvel : W.velocity = u)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W hWvel (t := t) (x := x) ht0 htT

theorem finite_time_witness_velocity_residual_curl_obstruction_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      hcurl

theorem explicit_global_output_exists_velocity_wrapper_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ ↔
      ∃ u : NSVelocityField,
        ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  exact ExplicitConcreteNavierStokesGlobalOutput_iff_exists_velocity

theorem explicit_global_output_with_velocity_pressure_residual_vorticity_zero_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  exact
    ExplicitConcreteNavierStokesGlobalOutputWithVelocity.spatialVorticity_momentumPressureResidual_zero
      (ν := ν) (u₀ := u₀) (u := u) h t x

theorem explicit_global_output_with_velocity_residual_curl_obstruction_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_of_momentumPressureResidual_vorticity_ne_zero
      hcurl

theorem generic_time_zero_nonintegrability_blocks_constant_field_bounded_energy_regression
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)

theorem generic_time_zero_nonintegrability_blocks_constant_field_bounded_energy_up_to_regression
    {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (constantVelocityField c) T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)
      hT

theorem generic_nonfinite_initial_energy_blocks_transport_full_drift_bounded_energy_up_to_regression
    {ν a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T := by
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (u := heatShearTransportFullDriftVelocityField ν a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)
      hT
      (matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c)

theorem constant_initial_velocity_global_output_exact_regression
    {ν : ℝ} {c : NSSpace} :
    ExplicitConcreteNavierStokesGlobalOutput ν (constantInitialVelocity c) ↔ c = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff

theorem constant_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) ↔ c = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff hν

theorem constant_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity c
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_constantInitialVelocity c x } ↔
      c = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff hν

theorem constant_initial_velocity_finite_initial_energy_exact_regression
    {c : NSSpace} :
    finiteInitialKineticEnergy (constantInitialVelocity c) ↔ c = 0 := by
  exact finiteInitialKineticEnergy_constantInitialVelocity_iff

theorem linear_shear_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) ↔ a = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity_iff

theorem linear_shear_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) ↔ a = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity_iff hν

theorem linear_shear_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity a
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity a
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity a x } ↔
      a = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity_iff hν

theorem linear_shear_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff

theorem linear_shear_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_iff hν

theorem linear_shear_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity a b c
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x } ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_iff hν

theorem linear_shear_initial_velocity_finite_initial_energy_exact_regression
    {a : ℝ} :
    finiteInitialKineticEnergy (linearShearInitialVelocity a) ↔
      a = 0 := by
  exact finiteInitialKineticEnergy_linearShearInitialVelocity_iff

theorem linear_shear_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearInitialVelocity a) T) ↔
      a = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity_iff hT

theorem linear_shear_vertical_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity_iff

theorem linear_shear_vertical_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_iff hν

theorem linear_shear_vertical_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity_iff hν

theorem linear_shear_vertical_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity_iff

theorem linear_shear_vertical_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearVerticalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity_iff hT

theorem linear_shear_horizontal_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity_iff

theorem linear_shear_horizontal_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_iff hν

theorem linear_shear_horizontal_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity_iff hν

theorem linear_shear_horizontal_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity_iff

theorem linear_shear_horizontal_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearHorizontalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity_iff hT

theorem linear_shear_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b c : ℝ} :
    finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff

theorem linear_shear_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearFullDriftInitialVelocity a b c) T) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff hT

theorem heat_shear_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity_iff

theorem heat_shear_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity_iff hν

theorem heat_shear_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity a k
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity a k
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity a k x } ↔
      a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity_iff hν

theorem heat_shear_initial_velocity_finite_initial_energy_exact_regression
    {a k : ℝ} :
    finiteInitialKineticEnergy (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearInitialVelocity_iff

theorem heat_shear_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearInitialVelocity a k) T) ↔
      a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity_iff hT

theorem heat_shear_streamwise_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k d : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity_iff

theorem heat_shear_streamwise_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff hν

theorem heat_shear_streamwise_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity a k d
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x } ↔
      d = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff hν

theorem heat_shear_streamwise_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k d : ℝ} :
    finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity_iff

theorem heat_shear_streamwise_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k d : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T) ↔
      d = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity_iff hT

theorem heat_shear_vertical_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity_iff

theorem heat_shear_vertical_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_iff hν

theorem heat_shear_vertical_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity a k c
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x } ↔
      c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity_iff hν

theorem heat_shear_vertical_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k c : ℝ} :
    finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity_iff

theorem heat_shear_vertical_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearVerticalDriftInitialVelocity a k c) T) ↔
      c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity_iff hT

theorem heat_shear_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff

theorem heat_shear_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff hν

theorem heat_shear_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity a k d c
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x } ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_iff hν

theorem heat_shear_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k d c : ℝ} :
    finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff

theorem heat_shear_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearFullDriftInitialVelocity a k d c) T) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff hT

theorem heat_shear_transport_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity_iff

theorem heat_shear_transport_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity_iff hν

theorem heat_shear_transport_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity a k b
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x } ↔
      b = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity_iff hν

theorem heat_shear_transport_initial_velocity_finite_initial_energy_exact_regression
    {a k b : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearTransportInitialVelocity_iff

theorem heat_shear_transport_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportInitialVelocity a k b) T) ↔
      b = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity_iff hT

theorem heat_shear_transport_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff

theorem heat_shear_transport_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_iff hν

theorem heat_shear_transport_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x } ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_iff hν

theorem heat_shear_transport_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k b d c : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff

theorem heat_shear_transport_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k b d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity_iff hT

theorem constant_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {c : NSSpace} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (constantInitialVelocity c) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_all

theorem linear_shear_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a b c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearFullDriftInitialVelocity a b c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all

theorem heat_shear_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearFullDriftInitialVelocity a k d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all

theorem heat_shear_transport_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_all

theorem constant_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace}
    (hfinite : finiteInitialKineticEnergy (constantInitialVelocity c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := constantInitialVelocity c
         smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_constantInitialVelocity c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_constantInitialVelocity_all
      hν hfinite

theorem linear_shear_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ}
    (hfinite : finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := linearShearFullDriftInitialVelocity a b c
         smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_all
      hν hfinite

theorem heat_shear_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearFullDriftInitialVelocity a k d c
         smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_all
      hν hfinite

theorem heat_shear_transport_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
         smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_all
      hν hfinite

end NavierStokesUniformVorticityContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
