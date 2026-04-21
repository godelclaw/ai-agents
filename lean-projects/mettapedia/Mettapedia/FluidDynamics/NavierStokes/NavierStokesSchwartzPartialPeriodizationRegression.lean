import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPartialPeriodization

/-!
# Navier-Stokes Schwartz Partial Periodization Regression

Small theorem-level checks for the finite partial-periodization prelude used in
the manuscript's large-torus Schwartz-data route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzPartialPeriodizationRegression

theorem empty_partialPeriodization_regression
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    finitePartialPeriodizationSchwartzInitialVelocity ∅ L u₀ = 0 := by
  ext x
  simp

theorem singleton_zero_partialPeriodization_regression
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    finitePartialPeriodizationSchwartzInitialVelocity ({0} : Finset NSLatticeIndex) L u₀ = u₀ := by
  ext x
  simp [periodizationShift_zero]

theorem periodizationShift_add_regression
    (L : ℝ) (m n : NSLatticeIndex) :
    periodizationShift L (m + n) =
      periodizationShift L m + periodizationShift L n :=
  periodizationShift_add L m n

theorem singleton_zero_partialPeriodization_divergenceFree_regression
    (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity
      ({0} : Finset NSLatticeIndex) L u₀ = u₀ := by
  ext x
  simp [finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity, periodizationShift_zero]

end NavierStokesSchwartzPartialPeriodizationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
