import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeAffinePressureExactObstruction

/-!
# Regression tests for finite-mode affine-pressure exact obstructions
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem oneOneTwoMode_affine_pressure_exact_witness_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∃ W : ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hclosure hbad

theorem oneOneTwoMode_affine_pressure_exact_global_output_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
        (affineAddScalarSchwartzPressure c π ρ q) := by
  exact
    not_exists_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hclosure hbad

theorem oneOneTwoMode_exact_surface_separation_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    (((∃ t x,
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
          (0 : NSSpace)) ∧
        ∃ W :
            ExplicitFiniteTimeRegularityWitness 0
              (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField)) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
          ∃ W : ExplicitFiniteTimeRegularityWitness
              ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
            W.velocity =
                twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
              W.pressure = affineAddScalarSchwartzPressure c π ρ q) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
          ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
            ν
            (twoModeSchwartzInitialVelocity 1 1 f g)
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
            (affineAddScalarSchwartzPressure c π ρ q) := by
  exact
    oneOneTwoModeSchwartzVelocity_exactSurfaceSeparation_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hfg hfDiv hgDiv hclosure hbad

end NavierStokes
end FluidDynamics
end Mettapedia
