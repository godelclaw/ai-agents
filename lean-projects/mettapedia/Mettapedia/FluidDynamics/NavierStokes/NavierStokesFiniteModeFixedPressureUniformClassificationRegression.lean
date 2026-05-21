import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureUniformClassification

/-!
# Finite-Mode Fixed-Pressure Uniform-Vorticity Classification Regression

Focused regression checks for the constructive fixed-pressure
uniform-vorticity classification on the constant-one two-mode branch.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeFixedPressureUniformClassificationRegression

theorem oneOne_twoMode_fixed_pressure_uniform_classification_regression
    {ν T : ℝ} (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hp : smoothSpaceTimePressure p)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_uniformVorticityData_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T) p f g hp hfDiv hgDiv hclosure

theorem oneOne_twoMode_affine_pressure_uniform_classification_regression
    {ν T : ℝ} (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_uniformVorticityData_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T) f g c π ρ q hc hπ hρ hfDiv hgDiv hclosure

theorem oneOne_twoMode_zeroPressure_uniform_classification_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        (0 : NSSpace) := by
  exact
    oneOneTwoModeSchwartzVelocity_zeroPressure_uniformVorticityData_iff_inviscidClosure_lapSum_zero_on
      (ν := ν) (T := T) hν f g hfDiv hgDiv hclosure

end NavierStokesFiniteModeFixedPressureUniformClassificationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
