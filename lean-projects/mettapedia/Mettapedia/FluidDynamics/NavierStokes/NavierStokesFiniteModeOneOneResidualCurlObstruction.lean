import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionUniformVorticityObstruction

/-!
# One-One Finite-Mode Residual-Curl Obstructions

This file upgrades the constant-one two-mode obstruction from fixed-pressure
mismatch arguments to the pressure-agnostic exact residual-curl surface.

Once the inviscid closure is supplied, the exact pressure residual of the same
velocity at viscosity `ν` is just the viscous Laplacian residual field.  If
that residual has nonzero vorticity at one slab point, then no pressure choice
can rescue the velocity as an exact witness, BKM datum, uniform-vorticity datum,
or prescribed-velocity whole-space output.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- On the inviscidly closed constant-one two-mode branch, the exact pressure
residual is exactly the viscous Laplacian residual field. -/
theorem momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    momentumPressureResidual ν
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) =
      (fun t x =>
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) := by
  funext t x
  unfold momentumPressureResidual
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
  simp [hclosure t x]

/-- The non-cancelling inviscid zero-pressure one-one branch already carries a
single finite-time witness that simultaneously supplies the exact witness,
explicit BKM envelope data, and an explicit uniform slab vorticity bound. -/
theorem
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_exhibits_exact_BKM_and_uniformPremises_of_convectionClosure
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
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          (∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  rcases
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
        (T := T) f g hfg hfDiv hgDiv hclosure with
    ⟨hnonzero, W, hWvel, hWpress, Ω, Bint, hEnv, hInt⟩
  have hω :
      uniformVorticityBoundUpTo W.velocity T
        (schwartzInitialVelocityVorticityBound f +
          schwartzInitialVelocityVorticityBound g) := by
    simpa [hWvel] using
      (uniformVorticityBoundUpTo_twoModeSchwartzVelocity_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp)
        (by intro t; simp))
  refine ⟨hnonzero, W, hWvel, hWpress, ?_, ?_⟩
  · exact ⟨Ω, Bint, hEnv, hInt⟩
  · exact ⟨_, hω⟩

/-- A nonzero residual-curl point on the inviscidly closed constant-one
two-mode branch blocks every exact finite-time witness with that velocity,
independently of pressure choice. -/
theorem
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
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
  refine
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ?_
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  refine ⟨t, x, ht0, htT, ?_⟩
  simpa [momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure
      (ν := ν) f g hclosure] using hne

/-- The BKM envelope layer cannot hide the same one-one residual-curl
obstruction either. -/
theorem
    not_exists_BKMData_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
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
        W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  refine
    not_exists_BKMData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ?_
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  refine ⟨t, x, ht0, htT, ?_⟩
  simpa [momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure
      (ν := ν) f g hclosure] using hne

/-- The older uniform-vorticity packaging layer adds no escape route either:
once the same velocity is impossible as an exact witness, adding a slab
vorticity bound cannot repair it. -/
theorem
    not_exists_uniformVorticityData_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
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
        W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  intro hW
  apply
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
      (ν := ν) (T := T) f g hclosure hcurl
  rcases hW with ⟨W, hWvel, _B, _hω⟩
  exact ⟨W, hWvel⟩

/-- A nonzero residual-curl point also blocks prescribed-velocity exact
whole-space outputs for the same one-one branch, regardless of pressure. -/
theorem
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
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
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity
        ν
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) := by
  refine
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_of_momentumPressureResidual_vorticity_ne_zero
      (ν := ν) (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ?_
  rcases hcurl with ⟨t, x, _ht0, _htT, hne⟩
  exact
    ⟨t, x, by
      simpa [momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure
        (ν := ν) f g hclosure] using hne⟩

/-- Route-level pressure-agnostic separation for the constant-one two-mode
branch: the non-cancelling inviscid zero-pressure witness already carries exact
fields, an explicit BKM envelope, and an explicit uniform vorticity bound, but
if the positive-viscosity residual field has nonzero vorticity at one slab
point, then no pressure choice can promote the same velocity to any of the
positive-viscosity exact/BKM/uniform/global surfaces. -/
theorem
    oneOneTwoModeSchwartzVelocity_pressureAgnosticSurfaceSeparation_of_inviscidClosure_residualVorticity_ne_zero_on
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_exhibits_exact_BKM_and_uniformPremises_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure
  · exact
      not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
        (ν := ν) (T := T) f g hclosure hcurl
  · exact
      not_exists_BKMData_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
        (ν := ν) (T := T) f g hclosure hcurl
  · exact
      not_exists_uniformVorticityData_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
        (ν := ν) (T := T) f g hclosure hcurl
  · exact
      not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero_on
        (ν := ν) (T := T) f g hclosure hcurl

end NavierStokes
end FluidDynamics
end Mettapedia
