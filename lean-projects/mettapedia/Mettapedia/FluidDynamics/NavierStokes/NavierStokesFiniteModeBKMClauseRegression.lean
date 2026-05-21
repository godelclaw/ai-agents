import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBKMClause

/-!
# Regression Tests for Finite-Mode BKM Clause Packaging
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeBKMClauseRegression

theorem two_mode_schwartz_zero_profile_BKM_clause_regression
    (ν T : ℝ) :
    ExplicitBKMContinuationClause
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
      T := by
  exact
    ExplicitBKMContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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

theorem two_mode_schwartz_zero_profile_repaired_BKM_clause_regression
    (ν T : ℝ) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
      T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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

theorem equal_amplitude_antiprofile_initial_BKM_clause_iff_zero_regression
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T ↔
      ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero ν T a0 f

theorem equal_amplitude_antiprofile_initial_BKM_clause_zero_side_regression
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T := by
  exact
    (ExplicitBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero
      ν T a0 f).2 (ExplicitBKMContinuationClause_zero ν T)

theorem equal_amplitude_antiprofile_initial_repaired_BKM_clause_iff_zero_regression
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T ↔
      ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero
      ν T a0 f

theorem equal_amplitude_antiprofile_initial_repaired_BKM_clause_zero_side_regression
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero
      ν T a0 f).2 (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)

end NavierStokesFiniteModeBKMClauseRegression
end NavierStokes
end FluidDynamics
end Mettapedia
