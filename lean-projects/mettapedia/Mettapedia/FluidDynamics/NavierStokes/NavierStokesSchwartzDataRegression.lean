import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzData
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Navier-Stokes Schwartz Data Regression

Small theorem-level checks for the manuscript-compatible Schwartz-data
restriction of the local whole-space Navier-Stokes target.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzDataRegression

theorem zero_schwartz_initialVelocity_smooth_regression :
    smoothInitialVelocityData ((0 : NSSchwartzInitialVelocity) : NSInitialVelocity) := by
  exact smoothInitialVelocityData_of_schwartzInitialVelocity 0

theorem zero_schwartz_initialVelocity_finiteEnergy_regression :
    finiteInitialKineticEnergy ((0 : NSSchwartzInitialVelocity) : NSInitialVelocity) := by
  exact finiteInitialKineticEnergy_of_schwartzInitialVelocity 0

theorem zero_schwartz_regularity_clause_regression
    (ν : ℝ) :
    ExplicitSchwartzAdmissibleNavierStokesRegularityClause
      ν (0 : NSSchwartzInitialVelocity) := by
  rw [ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff]
  simpa using ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν

theorem zero_schwartz_timeOnlyPressure_regularity_clause_regression
    (ν : ℝ) :
    ExplicitSchwartzAdmissibleNavierStokesRegularityClause
      ν (0 : NSSchwartzInitialVelocity) := by
  rw [ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff]
  simpa using
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
      ν
      (fun t : NSTime => t + 1)
      (by
        simpa using
          (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun t : NSTime => t + 1)))

end NavierStokesSchwartzDataRegression
end NavierStokes
end FluidDynamics
end Mettapedia
