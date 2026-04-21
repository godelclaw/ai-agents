import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Concrete Navier-Stokes Witness Construction Regression

Small theorem-level checks for the direct zero witness and the boxed steady
seed witness classification.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionRegression

theorem zero_global_witness_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact zeroNavierStokesGlobalRegularityWitness_nonempty hν

theorem boxed_steady_seed_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
      hν N L u₀ T p hp

end NavierStokesWitnessConstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
