import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyInequality
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Energy Inequality to Finite-Time Continuation Bridge

This file connects the corrected coordinatewise energy-identity lane to the
finite-time continuation surface.  The core energy file proves two-time kinetic
energy decay; here we package that decay as the `boundedKineticEnergyUpTo` slot
used by finite-time regularity witnesses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A corrected coordinatewise energy identity plus slice integrability on a
time slab supplies the finite-time bounded-energy predicate used by the
continuation surface.  The bound is the initial kinetic energy at time `0`. -/
theorem boundedKineticEnergyUpTo_of_coordinateEnergyDissipationIdentity_smooth_of_integrable_on_slab
    (u : NSVelocityField) (p : NSPressureField) {ν T : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    (hkin :
      ∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t)) :
    boundedKineticEnergyUpTo u T := by
  refine ⟨kineticEnergyAt u 0, kineticEnergyAt_nonneg u 0, ?_⟩
  intro t ht0 htT
  refine ⟨hkin t ht0 htT, ?_⟩
  exact
    coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
      (u := u)
      (p := p)
      (ν := ν)
      hν
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear
      (t₀ := 0)
      (t₁ := t)
      ht0

/-- A finite-energy initial datum gives uniform slab energy control for its
time-independent seed.  This closes the energy slot for the seed, without
claiming that the seed solves the Navier-Stokes momentum equation. -/
theorem boundedKineticEnergyUpTo_timeIndependentVelocity
    {u₀ : NSInitialVelocity} {T : ℝ}
    (hE : finiteInitialKineticEnergy u₀) :
    boundedKineticEnergyUpTo (timeIndependentVelocity u₀) T := by
  refine ⟨kineticEnergyAt (timeIndependentVelocity u₀) 0,
    kineticEnergyAt_nonneg (timeIndependentVelocity u₀) 0, ?_⟩
  intro t _ht0 _htT
  constructor
  · simpa [kineticEnergyDensity_timeIndependentVelocity, finiteInitialKineticEnergy] using hE
  · rw [kineticEnergyAt_timeIndependentVelocity,
      kineticEnergyAt_timeIndependentVelocity]

/-- Package the corrected energy identity as the bounded-energy slot of an
explicit finite-time regularity witness.  The PDE, smoothness, incompressibility
and initial-condition hypotheses are the other witness fields; the new work is
that `bounded_energy_on` is supplied by the energy inequality with initial
kinetic energy as the slab bound. -/
def ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (u : NSVelocityField) (p : NSPressureField)
    (hu : smoothSpaceTimeVelocity u)
    (hp : smoothSpaceTimePressure p)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    (hkin :
      ∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t))
    (hν : 0 ≤ ν)
    (hdiv : ∀ t x, spatialDivergence u t x = 0)
    (hinit : MatchesInitialVelocity u₀ u) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T where
  velocity := u
  pressure := p
  smooth_velocity := hu
  smooth_pressure := hp
  momentum_equation_on := by
    intro t x _ht0 _htT
    exact heq t x
  incompressible_on := by
    intro t x _ht0 _htT
    exact hdiv t x
  initial_condition := hinit
  bounded_energy_on :=
    boundedKineticEnergyUpTo_of_coordinateEnergyDissipationIdentity_smooth_of_integrable_on_slab
      u p hν hderiv heq hintegrable hviscous hboundary hnonlinear hkin

/-- Concrete finite-time bounded-energy bridge for the bounded two-profile
Schwartz class with affine plus localized Schwartz pressure.  The point is not
just that this class has a coarse coefficient bound; the corrected energy
identity gives the sharper slab bound by the initial kinetic energy. -/
theorem boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    (T : ℝ) :
    boundedKineticEnergyUpTo (fun s y => a s • f y + b s • g y) T := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  refine ⟨kineticEnergyAt u 0, kineticEnergyAt_nonneg u 0, ?_⟩
  intro t ht0 _htT
  have hmeaningful :
      Integrable (kineticEnergyDensity u t) ∧
        HasDerivAt (normalizedKineticEnergy u)
          (-(coordinateEnergyDissipationRate u ν t)) t := by
    simpa [u] using
      (meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
        a a' b b' f g A B c π ρ q ν haBound hbBound ha hb heq hdiv t)
  refine ⟨hmeaningful.1, ?_⟩
  have hbound :
      kineticEnergyAt (fun s y => a s • f y + b s • g y) t ≤
        kineticEnergyAt (fun s y => a s • f y + b s • g y) 0 :=
    (kineticEnergyAt_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv
      (t₀ := 0) (t₁ := t) ht0).2
  simpa [u] using hbound

/-- Concrete finite-time regularity witness constructor for the bounded
two-profile Schwartz class with affine plus localized Schwartz pressure.  The
smoothness and initial-match fields are kept explicit, while the
`bounded_energy_on` field is supplied by the corrected energy inequality. -/
def ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure
        ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
          fun s : NSTime => fun y : NSSpace => ρ s * q y))
    (hinit : MatchesInitialVelocity u₀ (fun s y => a s • f y + b s • g y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T where
  velocity := fun s y => a s • f y + b s • g y
  pressure :=
    (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
      fun s : NSTime => fun y : NSSpace => ρ s * q y
  smooth_velocity := hu
  smooth_pressure := hp
  momentum_equation_on := by
    intro t x _ht0 _htT
    exact heq t x
  incompressible_on := by
    intro t x _ht0 _htT
    exact hdiv t x
  initial_condition := hinit
  bounded_energy_on :=
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv T

end NavierStokes
end FluidDynamics
end Mettapedia
