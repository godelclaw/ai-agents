import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLocalExistencePrerequisites

/-!
# Boxed Periodization Local-Existence Prerequisites Regression

Small theorem-level checks for the boxed steady seed fields that do not require
solving the Navier-Stokes evolution equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzPeriodizationLocalExistencePrerequisitesRegression

theorem boundedKineticEnergyUpTo_boxedPartialPeriodizationSteadySeed_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    boundedKineticEnergyUpTo
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T := by
  exact boundedKineticEnergyUpTo_boxedPartialPeriodizationSteadySeed hν N L u₀ T

theorem boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (0 : NSPressureField) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T := by
  exact boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields hν N L u₀ T

end NavierStokesSchwartzPeriodizationLocalExistencePrerequisitesRegression
end NavierStokes
end FluidDynamics
end Mettapedia
