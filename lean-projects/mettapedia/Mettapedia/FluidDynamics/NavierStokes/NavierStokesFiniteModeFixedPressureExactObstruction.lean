import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction

/-!
# Finite-Mode Fixed-Pressure Exact Obstructions

This file strengthens the constant-one two-mode exact obstruction from the
affine-plus-localized pressure family to arbitrary fixed pressures.

Once the inviscid closure is supplied, any exact finite-time witness or exact
whole-space output with the same velocity must realize the entire viscous
Laplacian residual as its pressure gradient on the certified slab. Therefore a
single pressure-gradient mismatch point already blocks that exact surface,
independently of any structured pressure ansatz.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- On the inviscidly closed constant-one two-mode branch, any exact finite-time
witness with a fixed pressure must realize the viscous Laplacian residual as
that pressure gradient at each certified slab point. -/
theorem
    ExplicitFiniteTimeRegularityWitness.oneOneTwoModeSchwartzVelocity_pressureGradient_eq_lapSum_on_of_inviscidClosure
    {ν T : ℝ} {p : NSPressureField}
    {f g : NSSchwartzInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T)
    (hWvel :
      W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
    (hWpress : W.pressure = p)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialPressureGradient p t x =
      (ν : ℝ) •
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  have hmom := W.momentum_equation_on t x ht0 htT
  rw [hWvel, hWpress] at hmom
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at hmom
  simpa [hclosure t x] using hmom

/-- A single pressure-gradient mismatch point on the certified slab blocks any
exact finite-time witness with that fixed pressure on the inviscidly closed
constant-one two-mode branch. -/
theorem
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
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
          W.pressure = p := by
  intro hW
  rcases hW with ⟨W, hWvel, hWpress⟩
  rcases hbad with ⟨t, x, ht0, htT, hne⟩
  exact hne
    (W.oneOneTwoModeSchwartzVelocity_pressureGradient_eq_lapSum_on_of_inviscidClosure
      hWvel hWpress hclosure ht0 htT)

/-- In particular, positive viscosity cannot reuse the inviscid zero-pressure
constant-one branch as an exact finite-time witness if the summed viscous
Laplacian residual is nonzero somewhere on the slab. -/
theorem
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
  refine
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
      (ν := ν) (T := T) (p := 0) f g hclosure ?_
  rcases hlap with ⟨t, x, ht0, htT, hne⟩
  have hsmulne :
      (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
        (0 : NSSpace) := by
    intro hsmul
    exact hne ((smul_eq_zero.mp hsmul).resolve_left hν.ne')
  refine ⟨t, x, ht0, htT, ?_⟩
  simpa [spatialPressureGradient_zero] using hsmulne.symm

/-- The same fixed-pressure mismatch also blocks exact whole-space outputs, since
any exact global pair would restrict to a forbidden finite-time witness on the
certified slab. -/
theorem
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
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
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
        p := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
      (ν := ν)
      (T := T)
      (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      (p := p)
      (not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
        (ν := ν) (T := T) p f g hclosure hbad)

/-- Concrete whole-space version of the same zero-pressure obstruction:
positive viscosity cannot promote the inviscid zero-pressure constant-one
branch to an exact whole-space output once the summed viscous Laplacian
residual is nonzero somewhere on the slab. -/
theorem
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
      (ν := ν) (T := T) (p := 0) f g hclosure
      (by
        rcases hlap with ⟨t, x, ht0, htT, hne⟩
        have hsmulne :
            (ν : ℝ) •
                (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                  spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
              (0 : NSSpace) := by
          intro hsmul
          exact hne ((smul_eq_zero.mp hsmul).resolve_left hν.ne')
        refine ⟨t, x, ht0, htT, ?_⟩
        simpa [spatialPressureGradient_zero] using hsmulne.symm)

/-- Route-level exact-surface separation for the positive-viscosity zero-pressure
constant-one branch. The nonzero inviscid zero-pressure witness exists, but a
single nonzero summed viscous Laplacian residual point still blocks positive-
viscosity exact finite-time and exact whole-space zero-pressure realizations. -/
theorem
    oneOneTwoModeSchwartzVelocity_inviscidZeroPressure_and_not_posViscosity_exactSurface_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg
      · let W :=
            ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
              f g hfDiv hgDiv hclosure (T := T)
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
        exact ⟨W, rfl, hWpressure⟩
    · exact
        not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
          hν f g hclosure hlap
  · exact
      not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
        hν f g hclosure hlap

end NavierStokes
end FluidDynamics
end Mettapedia
