import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactClassification

/-!
# Finite-Mode Fixed-Pressure Exact Classification Regression

Focused regression checks for the constructive fixed-pressure exact
classification on the constant-one two-mode branch.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeFixedPressureExactClassificationRegression

theorem oneOne_twoMode_fixed_pressure_witness_classification_regression
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
          W.pressure = p) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T) p f g hp hfDiv hgDiv hclosure

theorem oneOne_twoMode_fixed_pressure_global_classification_regression
    {ν : ℝ} (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hp : smoothSpaceTimePressure p)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (twoModeSchwartzInitialVelocity 1 1 f g)
      (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      p ↔
      ∀ t x,
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_globalOutputWithVelocityPressure_iff_inviscidClosure_pressureGradient_lapSum
      (ν := ν) p f g hp hfDiv hgDiv hclosure

theorem oneOne_twoMode_affine_pressure_witness_classification_regression
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
          W.pressure = affineAddScalarSchwartzPressure c π ρ q) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_finiteTimeWitness_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T) f g c π ρ q hc hπ hρ hfDiv hgDiv hclosure

theorem oneOne_twoMode_affine_pressure_global_classification_regression
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
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
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (twoModeSchwartzInitialVelocity 1 1 f g)
      (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      (affineAddScalarSchwartzPressure c π ρ q) ↔
      ∀ t x,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_globalOutput_iff_inviscidClosure_pressureGradient_lapSum
      (ν := ν) f g c π ρ q hc hπ hρ hfDiv hgDiv hclosure

end NavierStokesFiniteModeFixedPressureExactClassificationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
