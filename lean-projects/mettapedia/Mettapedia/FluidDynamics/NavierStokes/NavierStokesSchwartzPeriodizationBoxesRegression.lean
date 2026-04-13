import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationBoxes

/-!
# Navier-Stokes Schwartz Periodization Boxes Regression

Theorem-level checks for the finite cubic-box exhaustion family used in the
manuscript's large-torus Schwartz-data route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzPeriodizationBoxesRegression

theorem centeredLatticeBox_zero_regression :
    centeredLatticeBox 0 = ({0} : Finset NSLatticeIndex) :=
  centeredLatticeBox_zero

theorem centeredLatticeBox_subset_succ_regression (N : ℕ) :
    centeredLatticeBox N ⊆ centeredLatticeBox (N + 1) :=
  centeredLatticeBox_mono (Nat.le_succ N)

theorem boxedPartialPeriodizedInitialVelocity_zero_regression
    (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPartialPeriodizedInitialVelocity 0 L u₀ = u₀ :=
  boxedPartialPeriodizedInitialVelocity_zero L u₀

theorem boxedPartialPeriodizationSchwartzInitialVelocity_zero_regression
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    boxedPartialPeriodizationSchwartzInitialVelocity 0 L u₀ = u₀ :=
  boxedPartialPeriodizationSchwartzInitialVelocity_zero L u₀

theorem boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_zero_regression
    (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity 0 L u₀ = u₀ :=
  boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_zero L u₀

end NavierStokesSchwartzPeriodizationBoxesRegression
end NavierStokes
end FluidDynamics
end Mettapedia
