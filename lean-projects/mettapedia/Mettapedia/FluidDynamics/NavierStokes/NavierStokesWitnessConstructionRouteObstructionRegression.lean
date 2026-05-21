import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionRouteObstruction

/-!
# Navier-Stokes Witness-Construction Route Obstruction Regression

Small theorem-level checks for the bundled exact-pair witness-construction
route obstruction.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionRouteObstructionRegression

theorem finite_time_witness_failure_blocks_exact_pair_route_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ExactPairWitnessConstructionRoute ν T u₀ u p := by
  exact not_ExactPairWitnessConstructionRoute_of_not_exists_finiteTimeWitness hW

theorem exact_pair_route_classification_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField} :
    ExactPairWitnessConstructionRoute ν T u₀ u p ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p := by
  exact ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness

theorem exact_pair_route_add_zero_spatial_gradient_pressure_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p q : NSPressureField}
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExactPairWitnessConstructionRoute ν T u₀ u (p + q) ↔
      ExactPairWitnessConstructionRoute ν T u₀ u p := by
  exact
    ExactPairWitnessConstructionRoute_iff_addPressureOfZeroSpatialGradient
      q hq hq_zero

theorem boxed_steady_seed_time_only_pressure_exact_pair_route_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
      hν N L u₀ π ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_exact_pair_route_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T π hπ

theorem boxed_steady_seed_exists_zero_spatial_gradient_pressure_exact_pair_route_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    (∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ExactPairWitnessConstructionRoute
            ν
            T
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T

theorem boxed_steady_seed_zero_spatial_gradient_pressure_exact_pair_route_iff_zero_pressure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p ↔
      ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ)) := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_zeroPressure
      hν N L u₀ T p hp hp_zero

theorem boxed_steady_seed_zero_spatial_gradient_pressure_exact_pair_route_failure_regression
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
          ExactPairWitnessConstructionRoute
            ν
            T
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail

theorem boxed_steady_seed_fixed_zero_spatial_gradient_pressure_exact_pair_route_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p := by
  exact
    not_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
      hν N L u₀ p hp hp_zero ht0 htT hfail

theorem boxed_steady_seed_zero_gradient_pressure_candidate_exact_pair_route_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      ¬ ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        p := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_exhibits_nonMomentumFiniteTimeAndGlobalFields_without_exactPairWitnessConstructionRoute
      hν N L u₀ T p hp hp_zero ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_candidate_exact_pair_route_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      ¬ ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeAndGlobalFields_without_exactPairWitnessConstructionRoute
      hν N L u₀ T π hπ ht0 htT hfail

end NavierStokesWitnessConstructionRouteObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
