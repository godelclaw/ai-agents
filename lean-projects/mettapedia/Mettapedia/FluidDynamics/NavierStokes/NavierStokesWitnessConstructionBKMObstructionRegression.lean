import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionBKMObstruction

/-!
# Navier-Stokes Witness-Construction BKM Obstruction Regression

Small theorem-level checks for lifting finite-time witness obstructions to the
BKM-packaged data surface.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionBKMObstructionRegression

theorem finite_time_witness_failure_lifts_to_BKM_data_failure_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact not_exists_BKMData_of_not_exists_finiteTimeWitness hW

theorem time_independent_velocity_stationary_failure_blocks_BKM_data_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_timeIndependentVelocity_BKMData_of_stationaryMomentum_failure
      ht0 htT hfail

theorem time_independent_schwartz_velocity_BKM_data_iff_stationary_regression
    {ν T : ℝ} (u₀ : NSSchwartzInitialVelocity) (p : NSPressureField)
    (hdiv : ∀ x, initialSpatialDivergence (u₀ : NSInitialVelocity) x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (u₀ : NSInitialVelocity) T,
        W.velocity = timeIndependentVelocity (u₀ : NSInitialVelocity) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x := by
  exact timeIndependentVelocity_schwartz_BKMData_iff_stationaryMomentum u₀ p hdiv hp

theorem boxed_steady_seed_BKM_data_iff_stationary_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  exact
    boxedPartialPeriodizationSteadySeed_BKMData_iff_stationaryMomentum
      hν N L u₀ T p hp

theorem boxed_steady_seed_time_only_pressure_BKM_data_iff_zero_pressure_stationary_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_BKMData_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T π hπ

theorem boxed_steady_seed_exists_zero_gradient_pressure_BKM_data_iff_zero_pressure_stationary_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    (∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ∃ W :
            ExplicitFiniteTimeRegularityWitness ν
              (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
            W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
              W.pressure = p ∧
              ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
                vorticityEnvelopeOn W.velocity T Ω ∧
                  integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  exact
    exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T

theorem boxed_steady_seed_time_only_pressure_BKM_data_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_BKMData_of_stationaryMomentum_failure
      hν N L u₀ π ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_candidate_BKM_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T) ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
          W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
            ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T B := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_BKMData
      hν N L u₀ T π hπ ht0 htT hfail

end NavierStokesWitnessConstructionBKMObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
