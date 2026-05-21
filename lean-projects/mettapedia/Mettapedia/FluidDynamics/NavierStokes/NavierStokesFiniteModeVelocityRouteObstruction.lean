import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeOneOneResidualCurlObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionVelocityRouteObstruction

/-!
# One-One Finite-Mode Velocity-Route Obstruction

This file specializes the bundled pressure-agnostic witness-construction
velocity route to the constant-one two-mode finite-mode branch.

The inviscidly closed branch already carries a concrete inviscid route
inhabitant. Conversely, if the positive-viscosity exact pressure residual has
nonzero vorticity at one slab point, then the bundled positive-viscosity route
collapses along with the exact, uniform-vorticity, BKM, and global-output
branches.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The non-cancelling inviscid constant-one two-mode branch already inhabits
the bundled pressure-agnostic witness-construction velocity route, and the
route witness is nontrivial. -/
theorem
    oneOneTwoModeSchwartzVelocity_nonzero_and_inviscidZeroPressure_exhibits_velocityRoute_of_convectionClosure
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      VelocityWitnessConstructionRoute
        0
        T
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) := by
  rcases
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_exhibits_exact_BKM_and_uniformPremises_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure with
    ⟨hnonzero, W, hWvel, _hWpress, _hBKM, _hω⟩
  refine ⟨hnonzero, ?_⟩
  exact Or.inl ⟨W, hWvel⟩

/-- A nonzero residual-curl point on the inviscidly closed constant-one two-mode
branch blocks the whole bundled pressure-agnostic witness-construction route
for the same velocity at viscosity `ν`. -/
theorem
    not_VelocityWitnessConstructionRoute_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
    {ν T : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialVorticity
            (fun s y =>
              (ν : ℝ) •
                (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
                  spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
            0) :
    ¬ VelocityWitnessConstructionRoute
      ν
      T
      (twoModeSchwartzInitialVelocity 1 1 f g)
      (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) := by
  refine
    not_VelocityWitnessConstructionRoute_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν)
      (T := T)
      (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      ?_
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  refine ⟨t, x, ht0, htT, ?_⟩
  simpa [momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure
      (ν := ν) f g hclosure] using hne

/-- Concrete pressure-agnostic route separation on the constant-one two-mode
branch: the inviscidly closed non-cancelling witness already occupies the full
bundled route at viscosity `0`, but a nonzero residual-curl point forbids the
same velocity from occupying that route at viscosity `ν`. -/
theorem
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidVelocityRoute_and_not_posViscosity_velocityRoute_of_inviscidClosure_residualVorticity_ne_zero_on
    {ν T : ℝ} (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialVorticity
            (fun s y =>
              (ν : ℝ) •
                (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
                  spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
            0) :
    ((∃ t x,
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
          (0 : NSSpace)) ∧
        VelocityWitnessConstructionRoute
          0
          T
          (twoModeSchwartzInitialVelocity 1 1 f g)
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)) ∧
      ¬ VelocityWitnessConstructionRoute
        ν
        T
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) := by
  refine ⟨?_, ?_⟩
  · exact
      oneOneTwoModeSchwartzVelocity_nonzero_and_inviscidZeroPressure_exhibits_velocityRoute_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure
  · exact
      not_VelocityWitnessConstructionRoute_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
        (ν := ν) (T := T) f g hclosure hcurl

end NavierStokes
end FluidDynamics
end Mettapedia
