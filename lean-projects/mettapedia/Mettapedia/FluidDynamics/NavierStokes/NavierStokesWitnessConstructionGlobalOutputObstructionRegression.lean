import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction

/-!
# Navier-Stokes Witness-Construction Global-Output Obstruction Regression

Small theorem-level checks for lifting finite-time witness obstructions to the
exact whole-space output surface for a fixed velocity/pressure pair.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionGlobalOutputObstructionRegression

theorem finite_time_witness_failure_blocks_exact_global_output_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
      hW

theorem time_independent_velocity_stationary_failure_blocks_exact_global_output_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν u₀ (timeIndependentVelocity u₀) p := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_timeIndependentVelocity_of_stationaryMomentum_failure
      ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_exact_global_output_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_of_stationaryMomentum_failure
      hν N L u₀ π ht0 htT hfail

theorem boxed_steady_seed_any_zero_gradient_pressure_exact_global_output_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
            ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p := by
  exact
    not_exists_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail

theorem boxed_steady_seed_zero_gradient_pressure_candidate_exact_global_output_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        p := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_exhibits_nonMomentumGlobalFields_without_exactGlobalOutput
      hν N L u₀ p hp hp_zero ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_candidate_exact_global_output_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {T : ℝ} {t : NSTime} {x : NSSpace}
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
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumGlobalFields_without_exactGlobalOutput
      hν N L u₀ π hπ ht0 htT hfail

end NavierStokesWitnessConstructionGlobalOutputObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
