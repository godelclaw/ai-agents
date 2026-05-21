import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeUniformClause

/-!
# Regression Tests for Finite-Mode Uniform Continuation Clause Packaging
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeUniformClauseRegression

theorem two_mode_schwartz_zero_profile_uniform_clause_regression
    (ν T : ℝ) :
    ExplicitUniformVorticityContinuationClause
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
      T := by
  exact
    ExplicitUniformVorticityContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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

theorem two_mode_schwartz_zero_profile_repaired_uniform_clause_regression
    (ν T : ℝ) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
      T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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

end NavierStokesFiniteModeUniformClauseRegression
end NavierStokes
end FluidDynamics
end Mettapedia
