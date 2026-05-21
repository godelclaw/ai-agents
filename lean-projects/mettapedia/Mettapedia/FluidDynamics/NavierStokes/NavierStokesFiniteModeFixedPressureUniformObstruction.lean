import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionUniformVorticityObstruction

/-!
# Finite-Mode Fixed-Pressure Uniform-Vorticity Obstructions

This file lifts the constant-one two-mode fixed-pressure exact obstruction to
the older uniform-vorticity-packaged finite-time surface.

The obstruction is unchanged: once the inviscid closure is supplied, any
positive-viscosity realization of the same velocity must realize the full
viscous Laplacian residual as its pressure gradient on the slab. Adding a
uniform slab vorticity bound does not weaken that exact witness obligation.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A single pressure-gradient mismatch point on the certified slab blocks any
uniform-vorticity-packaged realization of the inviscidly closed constant-one
two-mode branch with that fixed pressure. -/
theorem
    not_exists_uniformVorticityData_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
    {ν T : ℝ} (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x,
        0 ≤ t ∧ t ≤ T ∧
          spatialPressureGradient p t x ≠
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness
      (not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
        (ν := ν) (T := T) p f g hclosure hbad)

/-- In particular, positive viscosity cannot reuse the inviscid zero-pressure
constant-one branch as uniform-vorticity data if the summed viscous Laplacian
residual is nonzero somewhere on the slab. -/
theorem
    not_exists_uniformVorticityData_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
          W.pressure = (0 : NSPressureField) ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness
      (not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
        (ν := ν) (T := T) hν f g hclosure hlap)

/-- Route-level uniform-vorticity separation for the positive-viscosity
zero-pressure constant-one branch. The nonzero inviscid zero-pressure witness
already carries an explicit uniform vorticity bound, but a single nonzero
summed viscous Laplacian residual point blocks every positive-viscosity
uniform-vorticity-packaged reuse of that same branch. -/
theorem
    oneOneTwoModeSchwartzVelocity_inviscidZeroPressure_uniformVorticityPremise_and_not_exists_posViscosity_uniformVorticityData_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
    ((∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField) ∧
            ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  constructor
  · refine ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg, ?_⟩
    let W :=
      ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
        f g hfDiv hgDiv hclosure (T := T)
    have hWvel :
        W.velocity =
          twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
      rfl
    have hWpressureAffine :
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) := by
      rfl
    have hWpressure : W.pressure = (0 : NSPressureField) := by
      have hAffineZero :
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
            (0 : NSPressureField) := by
        funext t x
        simp [affineAddScalarSchwartzPressure]
      exact hWpressureAffine.trans hAffineZero
    have hω :
        uniformVorticityBoundUpTo W.velocity T
          (schwartzInitialVelocityVorticityBound f +
            schwartzInitialVelocityVorticityBound g) := by
      simpa [hWvel] using
        (uniformVorticityBoundUpTo_twoModeSchwartzVelocity_of_abs_le
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
          (by intro t; simp)
          (by intro t; simp))
    exact
      ⟨W, hWvel, hWpressure, _, hω⟩
  · exact
      not_exists_uniformVorticityData_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
        (ν := ν) (T := T) hν f g hclosure hlap

end NavierStokes
end FluidDynamics
end Mettapedia
