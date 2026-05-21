import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeOneOneResidualCurlObstruction

/-!
# One-One finite-mode residual-curl obstruction regression

Focused regression checks for the pressure-agnostic one-one residual-curl
obstruction surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeOneOneResidualCurlObstructionRegression

theorem oneOne_twoMode_residual_curl_no_exact_witness_regression
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
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
      (ν := ν) (T := T) f g hclosure hcurl

theorem oneOne_twoMode_pressureAgnostic_surface_separation_regression
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
    (((∃ t x,
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
          (0 : NSSpace)) ∧
        ∃ W :
            ExplicitFiniteTimeRegularityWitness 0
              (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField) ∧
            (∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint) ∧
            ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ∧
      (¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ∧
      (¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T B) ∧
      (¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity
          ν
          (twoModeSchwartzInitialVelocity 1 1 f g)
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)) := by
  exact
    oneOneTwoModeSchwartzVelocity_pressureAgnosticSurfaceSeparation_of_inviscidClosure_residualVorticity_ne_zero_on
      (ν := ν) (T := T) f g hfg hfDiv hgDiv hclosure hcurl

end NavierStokesFiniteModeOneOneResidualCurlObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
