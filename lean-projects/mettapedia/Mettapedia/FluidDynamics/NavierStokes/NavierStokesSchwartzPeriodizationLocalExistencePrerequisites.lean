import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyContinuationBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationConvergence

/-!
# Boxed Periodization Local-Existence Prerequisites

This file records the non-evolution fields available for the steady seed
attached to boxed Schwartz periodization data.  It deliberately stops short of
constructing an `ExplicitFiniteTimeRegularityWitness`: the missing field is the
Navier-Stokes momentum equation, which requires an actual local PDE existence
construction rather than the time-independent compatibility seed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BoxedPeriodizationLocalExistencePrerequisites

open scoped ContDiff

/-- The steady seed attached to boxed periodized data has uniform finite-energy
control on every slab.  The proof uses the finite-energy metadata already
carried by the boxed `FiniteEnergyAdmissibleNavierStokesProblemData`. -/
theorem boundedKineticEnergyUpTo_boxedPartialPeriodizationSteadySeed
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    boundedKineticEnergyUpTo
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T := by
  simpa [boxedPartialPeriodizationSteadySeedVelocity,
    boxedPartialPeriodizationNavierStokesProblemData,
    FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData] using
    boundedKineticEnergyUpTo_timeIndependentVelocity
      (u₀ := (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).initialVelocity)
      (T := T)
      (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).finite_initial_energy

/-- All non-momentum fields needed for a finite-time witness are available for
the boxed steady seed.  The remaining missing field is precisely the PDE
momentum equation, so this theorem is a checklist of prerequisites rather than
a local-existence theorem. -/
theorem boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields
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
  rcases boxedPartialPeriodizationSteadySeed_basic hν N L u₀ with
    ⟨hsmooth, hinit, hdiv, _htime, _henergyDensity⟩
  exact ⟨hsmooth, by simpa using smoothSpaceTimePressure_const (0 : ℝ),
    hdiv, hinit, boundedKineticEnergyUpTo_boxedPartialPeriodizationSteadySeed hν N L u₀ T⟩

end BoxedPeriodizationLocalExistencePrerequisites

end NavierStokes
end FluidDynamics
end Mettapedia
