import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzDivergenceFreeBridge

/-!
# Finite-Mode Schwartz Divergence-Free Bridge Regression

Regression checks for the bridge from bounded two-mode Schwartz ansatzes to the
manuscript-style `Sσ(ℝ^3)` clause surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzDivergenceFreeBridgeRegression

theorem two_mode_schwartz_divergence_free_zero_bridge_explicit_regression
    (ν : ℝ) :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause
      ν
      (twoModeSchwartzDivergenceFreeInitialVelocity
        0 0
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (by intro x; simpa using initialSpatialDivergence_zero x)
        (by intro x; simpa using initialSpatialDivergence_zero x)) := by
  exact
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_twoModeSchwartzDivergenceFreeInitialVelocity_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      contDiff_const contDiff_const
      (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
      0 0
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (0 : 𝓢(NSSpace, ℝ))
      contDiff_const contDiff_const contDiff_const
      (by intro t; simp)
      (by intro t; simp)
      (by intro x; simpa using initialSpatialDivergence_zero x)
      (by intro x; simpa using initialSpatialDivergence_zero x)
      (by
        intro t x
        simpa using
          momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
            ν (fun _ : NSTime => 0)
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (0 : 𝓢(NSSpace, ℝ)) t x)

theorem two_mode_schwartz_divergence_free_zero_bridge_structured_regression
    (ν : ℝ) :
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause
      ν
      (twoModeSchwartzDivergenceFreeInitialVelocity
        0 0
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (by intro x; simpa using initialSpatialDivergence_zero x)
        (by intro x; simpa using initialSpatialDivergence_zero x)) := by
  exact
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_twoModeSchwartzDivergenceFreeInitialVelocity_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      contDiff_const contDiff_const
      (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
      0 0
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (0 : 𝓢(NSSpace, ℝ))
      contDiff_const contDiff_const contDiff_const
      (by intro t; simp)
      (by intro t; simp)
      (by intro x; simpa using initialSpatialDivergence_zero x)
      (by intro x; simpa using initialSpatialDivergence_zero x)
      (by
        intro t x
        simpa using
          momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
            ν (fun _ : NSTime => 0)
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (0 : 𝓢(NSSpace, ℝ)) t x)

end NavierStokesFiniteModeSchwartzDivergenceFreeBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
