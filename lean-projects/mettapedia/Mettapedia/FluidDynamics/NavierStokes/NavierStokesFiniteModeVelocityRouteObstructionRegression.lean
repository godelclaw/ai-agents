import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVelocityRouteObstruction

/-!
# One-One Finite-Mode Velocity-Route Obstruction Regression

Focused regression checks for the bundled pressure-agnostic finite-mode
velocity-route obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeVelocityRouteObstructionRegression

theorem oneOne_twoMode_residual_curl_no_velocity_route_regression
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
  exact
    not_VelocityWitnessConstructionRoute_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
      (ν := ν) (T := T) f g hclosure hcurl

theorem oneOne_twoMode_velocity_route_separation_regression
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
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidVelocityRoute_and_not_posViscosity_velocityRoute_of_inviscidClosure_residualVorticity_ne_zero_on
      (ν := ν) (T := T) f g hfg hfDiv hgDiv hclosure hcurl

end NavierStokesFiniteModeVelocityRouteObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
