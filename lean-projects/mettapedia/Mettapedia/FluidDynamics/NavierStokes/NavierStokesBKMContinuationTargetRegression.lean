import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget

/-!
# Navier-Stokes BKM Continuation Target Regression

Small theorem-level checks for the unrepaired BKM target obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesBKMContinuationTargetRegression

theorem BKM_data_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 := by
  exact
    BKMData_momentumPressureResidual_vorticity_zero_on
      (ν := ν) (T := T) (u₀ := u₀) (W := W) hBKM (t := t) (x := x) ht0 htT

theorem BKM_data_velocity_eq_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (hWvel : W.velocity = u)
    (hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  exact
    BKMData_momentumPressureResidual_vorticity_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) (u := u) (W := W) hWvel hBKM
      (t := t) (x := x) ht0 htT

theorem BKM_data_velocity_residual_curl_obstruction_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_BKMData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      hcurl

theorem unrepaired_BKM_target_negative_horizon_regression :
    ¬ ExplicitBKMContinuationTarget := by
  exact not_ExplicitBKMContinuationTarget

theorem transported_heat_shear_unit_exp_BKM_envelope_regression :
    vorticityEnvelopeOn (heatShearTransportVelocityField 0 1 1 1) 1
        (heatShearExpVorticityEnvelope 0 1 1) ∧
      integrableVorticityEnvelopeOn (heatShearExpVorticityEnvelope 0 1 1) 1 1 := by
  simpa using heatShearTransportVelocityField_has_expBKMEnvelope 0 1 1 1 1
    (by norm_num) (by norm_num)

theorem unit_heat_shear_exp_envelope_exact_integral_regression :
    (∫ t in Set.Icc 0 (1 : ℝ), heatShearExpVorticityEnvelope 1 1 1 t
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      heatShearExpVorticityEnvelopeExactIntegralBound 1 1 1 1 := by
  simpa using
    integral_heatShearExpVorticityEnvelope_eq_exactIntegralBound 1 1 1 1
      (by norm_num) (by norm_num)

theorem transported_full_drift_heat_shear_unit_exact_exp_BKM_envelope_regression :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) 1
        (heatShearExpVorticityEnvelope 1 1 1) ∧
      integrableVorticityEnvelopeOn (heatShearExpVorticityEnvelope 1 1 1) 1
        (heatShearExpVorticityEnvelopeExactIntegralBound 1 1 1 1) := by
  simpa using heatShearTransportFullDriftVelocityField_has_exactExpBKMEnvelope
    1 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)

end NavierStokesBKMContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
