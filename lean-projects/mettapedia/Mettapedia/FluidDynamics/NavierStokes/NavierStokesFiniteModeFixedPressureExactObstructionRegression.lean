import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactObstruction

/-!
# Finite-Mode Fixed-Pressure Exact Obstruction Regression

Focused regression checks for the fixed-pressure exact witness/global-output
obstructions on the constant-one two-mode branch.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeFixedPressureExactObstructionRegression

theorem oneOneTwoMode_zeroPressure_exact_witness_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hlap : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x ≠
          (0 : NSSpace)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
      hν f g hclosure hlap

theorem oneOneTwoMode_zeroPressure_exact_global_output_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hlap : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x ≠
          (0 : NSSpace)) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
        (0 : NSPressureField) := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
      hν f g hclosure hlap

theorem oneOneTwoMode_zeroPressure_exact_surface_separation_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hlap : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x ≠
          (0 : NSSpace)) :
    (((∃ t x,
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
          (0 : NSSpace)) ∧
        ∃ W :
            ExplicitFiniteTimeRegularityWitness 0
              (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField)) ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField)) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
          ν
          (twoModeSchwartzInitialVelocity 1 1 f g)
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
          (0 : NSPressureField) := by
  exact
    oneOneTwoModeSchwartzVelocity_inviscidZeroPressure_and_not_posViscosity_exactSurface_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
      hν f g hfg hfDiv hgDiv hclosure hlap

end NavierStokesFiniteModeFixedPressureExactObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
