import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactObstruction

/-!
# Finite-Mode Fixed-Pressure Exact Classification

This file complements the fixed-pressure exact obstructions on the constant-one
two-mode branch with the corresponding constructive classification theorems.

Once the inviscid closure is supplied, a fixed smooth pressure promotes the
same velocity to an exact finite-time witness precisely when its spatial
gradient supplies the missing viscous Laplacian residual on the certified slab.
Likewise, a fixed smooth pressure promotes the same velocity to an exact
whole-space output precisely when that compensation identity holds everywhere.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Exact finite-time witness classification for the inviscidly closed
constant-one two-mode branch with a fixed smooth pressure.  On a slab, the
only missing analytic condition is that the pressure gradient supply the
viscous Laplacian residual pointwise. -/
theorem oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
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
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    exact
      W.oneOneTwoModeSchwartzVelocity_pressureGradient_eq_lapSum_on_of_inviscidClosure
        hWvel hWpress hclosure ht0 htT
  · intro hpressure
    refine ⟨{
      velocity := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g
      pressure := p
      smooth_velocity :=
        smoothSpaceTimeVelocity_twoModeSchwartzVelocity
          contDiff_const contDiff_const f g
      smooth_pressure := hp
      momentum_equation_on := ?_
      incompressible_on := ?_
      initial_condition := MatchesInitialVelocity_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g
      bounded_energy_on := ?_
    }, rfl, rfl⟩
    · intro t x ht0 htT
      rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
          (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
          contDiff_const contDiff_const f g t x,
        spatialConvection_twoModeSchwartzVelocity
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
        spatialLaplacian_twoModeSchwartzVelocity
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
      simpa [hclosure t x] using hpressure t x ht0 htT
    · intro t x _ht0 _htT
      simpa using
        (spatialDivergence_twoModeSchwartzVelocity_zero
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g hfDiv hgDiv t x)
    · simpa [twoModeSchwartzVelocity, timeIndependentVelocity, twoModeSchwartzInitialVelocity] using
        (boundedKineticEnergyUpTo_timeIndependentVelocity
          (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
          (T := T)
          (finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity 1 1 f g))

/-- Exact whole-space output classification for the inviscidly closed
constant-one two-mode branch with a fixed smooth pressure.  Globally, the same
velocity/pressure pair exists exactly when the pressure gradient supplies the
viscous Laplacian residual at every spacetime point. -/
theorem oneOneTwoModeSchwartzVelocity_globalOutputWithVelocityPressure_iff_inviscidClosure_pressureGradient_lapSum
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
  constructor
  · intro hGlobal t x
    rcases hGlobal with ⟨_hu, _hp, hmom, _hinc, _hinit, _hbd⟩
    have hmomtx := hmom t x
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at hmomtx
    simpa [hclosure t x] using hmomtx
  · intro hpressure
    refine ⟨smoothSpaceTimeVelocity_twoModeSchwartzVelocity
      contDiff_const contDiff_const f g, hp, ?_, ?_, ?_, ?_⟩
    · intro t x
      rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
          (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
          contDiff_const contDiff_const f g t x,
        spatialConvection_twoModeSchwartzVelocity
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
        spatialLaplacian_twoModeSchwartzVelocity
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
      simpa [hclosure t x] using hpressure t x
    · intro t x
      simpa using
        (spatialDivergence_twoModeSchwartzVelocity_zero
          (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g hfDiv hgDiv t x)
    · exact MatchesInitialVelocity_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g
    · simpa [twoModeSchwartzVelocity, timeIndependentVelocity, twoModeSchwartzInitialVelocity] using
        (boundedKineticEnergy_timeIndependentVelocity
          (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
          (finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity 1 1 f g))

/-- Manuscript-facing finite-time witness classification specialized to the
affine-plus-localized Schwartz pressure family. -/
theorem
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_finiteTimeWitness_iff_inviscidClosure_pressureGradient_lapSum_on
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
    oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T)
      (p := affineAddScalarSchwartzPressure c π ρ q)
      f g
      (smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q)
      hfDiv hgDiv hclosure

/-- Manuscript-facing exact global-output classification specialized to the
affine-plus-localized Schwartz pressure family. -/
theorem
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_globalOutput_iff_inviscidClosure_pressureGradient_lapSum
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
    oneOneTwoModeSchwartzVelocity_globalOutputWithVelocityPressure_iff_inviscidClosure_pressureGradient_lapSum
      (ν := ν)
      (p := affineAddScalarSchwartzPressure c π ρ q)
      f g
      (smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q)
      hfDiv hgDiv hclosure

end NavierStokes
end FluidDynamics
end Mettapedia
