import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDivergenceFreeData
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Navier-Stokes Schwartz Divergence-Free Data Regression

Small theorem-level checks for the manuscript-style `Sσ(ℝ^3)` restriction of
the local whole-space Navier-Stokes target.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzDivergenceFreeDataRegression

/-- Zero data inhabit the manuscript-style `Sσ(ℝ^3)` input class. -/
def zeroSchwartzDivergenceFreeInitialVelocity :
    NSSchwartzDivergenceFreeInitialVelocity :=
  ⟨0, by
    intro x
    simpa using (initialSpatialDivergence_zero x)⟩

theorem zero_schwartzDivergenceFree_initialVelocity_smooth_regression :
    smoothInitialVelocityData
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) := by
  exact
    smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity
      zeroSchwartzDivergenceFreeInitialVelocity

theorem zero_schwartzDivergenceFree_initialVelocity_finiteEnergy_regression :
    finiteInitialKineticEnergy
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) := by
  exact
    finiteInitialKineticEnergy_of_schwartzDivergenceFreeInitialVelocity
      zeroSchwartzDivergenceFreeInitialVelocity

theorem zero_schwartzDivergenceFree_initialVelocity_divergence_regression
    (x : NSSpace) :
    initialSpatialDivergence
        (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) x = 0 := by
  exact
    divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity
      zeroSchwartzDivergenceFreeInitialVelocity x

theorem zero_schwartzDivergenceFree_regularity_clause_regression
    (ν : ℝ) :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause
      ν zeroSchwartzDivergenceFreeInitialVelocity := by
  rw [ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff]
  simpa using ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν

theorem zero_structured_schwartzDivergenceFree_regularity_clause_regression
    (ν : ℝ) :
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause
      ν zeroSchwartzDivergenceFreeInitialVelocity := by
  exact
    (StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_iff
      (ν := ν) (u₀ := zeroSchwartzDivergenceFreeInitialVelocity)).2
      (zero_schwartzDivergenceFree_regularity_clause_regression ν)

theorem zero_schwartzDivergenceFree_timeOnlyPressure_regularity_clause_regression
    (ν : ℝ) :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause
      ν zeroSchwartzDivergenceFreeInitialVelocity := by
  rw [ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff]
  simpa using
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
      ν
      (fun t : NSTime => t + 1)
      (by
        simpa using
          (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun t : NSTime => t + 1)))

end NavierStokesSchwartzDivergenceFreeDataRegression
end NavierStokes
end FluidDynamics
end Mettapedia
