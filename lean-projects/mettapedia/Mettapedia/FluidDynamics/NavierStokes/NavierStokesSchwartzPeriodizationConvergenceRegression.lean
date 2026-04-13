import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationConvergence

/-!
# Navier-Stokes Schwartz Periodization Convergence Regression

Small theorem-level checks for the local cube convergence interface above the
finite box periodization family.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzPeriodizationConvergenceRegression

open Filter

/-- Zero data inhabit the manuscript-style `Sσ(ℝ^3)` input class. -/
def zeroSchwartzDivergenceFreeInitialVelocity :
    NSSchwartzDivergenceFreeInitialVelocity :=
  ⟨0, by
    intro x
    simpa using (initialSpatialDivergence_zero x)⟩

theorem boxedPartialPeriodizationConvergesOnCube_zero_regression
    (R L : ℝ) :
    BoxedPartialPeriodizationConvergesOnCube R L
      (0 : NSInitialVelocity) (0 : NSInitialVelocity) := by
  intro x hx
  simp [boxedPartialPeriodizedInitialVelocity, finitePartialPeriodizedInitialVelocity]

theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_zero_regression
    (R L : ℝ) :
    ∀ x ∈ spatialCube R,
      Filter.Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (0 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
    (boxedPartialPeriodizationConvergesOnCube_zero_regression R L)

theorem boxedPartialPeriodizationConvergesOnCube_zero_schwartzDivergenceFree_regression
    (R L : ℝ) :
    BoxedPartialPeriodizationConvergesOnCube R L
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity)
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) := by
  simpa using boxedPartialPeriodizationConvergesOnCube_zero_regression R L

end NavierStokesSchwartzPeriodizationConvergenceRegression
end NavierStokes
end FluidDynamics
end Mettapedia
