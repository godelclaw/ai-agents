import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionBKMObstruction

/-!
# Finite-Mode Fixed-Pressure BKM Obstructions

This file lifts the constant-one two-mode fixed-pressure exact obstruction to
the BKM-packaged continuation surface.

The key point is unchanged: once the inviscid closure is supplied, any
positive-viscosity realization of the same velocity must realize the full
viscous Laplacian residual as its pressure gradient on the slab. Adding a BKM
envelope and integral budget does not weaken that exact witness obligation.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A single pressure-gradient mismatch point on the certified slab blocks any
BKM-packaged realization of the inviscidly closed constant-one two-mode branch
with that fixed pressure. -/
theorem
    not_exists_BKMData_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
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
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_of_not_exists_finiteTimeWitness
      (not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_pressure_of_inviscidClosure_pressureGradient_lapSum_mismatch_on
        (ν := ν) (T := T) p f g hclosure hbad)

/-- In particular, positive viscosity cannot reuse the inviscid zero-pressure
constant-one branch as BKM data if the summed viscous Laplacian residual is
nonzero somewhere on the slab. -/
theorem
    not_exists_BKMData_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_of_not_exists_finiteTimeWitness
      (not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
        (ν := ν) (T := T) hν f g hclosure hlap)

/-- Route-level BKM separation for the positive-viscosity zero-pressure
constant-one branch. The nonzero inviscid zero-pressure BKM premise exists, but
a single nonzero summed viscous Laplacian residual point blocks every
positive-viscosity BKM-packaged reuse of that same zero-pressure branch. -/
theorem
    oneOneTwoModeSchwartzVelocity_inviscidZeroPressure_BKMPremise_and_not_exists_posViscosity_BKMData_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
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
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity = twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField) ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · exact
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure
  · exact
      not_exists_BKMData_oneOneTwoModeSchwartzVelocity_zeroPressure_of_inviscidClosure_lapSum_ne_zero_on
        (ν := ν) (T := T) hν f g hclosure hlap

end NavierStokes
end FluidDynamics
end Mettapedia
