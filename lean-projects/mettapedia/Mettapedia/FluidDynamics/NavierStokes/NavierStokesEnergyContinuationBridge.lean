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

/-- The slab kinetic-integrability hypothesis used by the energy/continuation
bridge already forces finite initial kinetic energy for the prescribed datum,
because it includes integrability at time `0` on every nonnegative slab. -/
theorem finiteInitialKineticEnergy_of_matchesInitialVelocity_of_kineticIntegrabilityOnSlab
    {u : NSVelocityField} {u₀ : NSInitialVelocity} {T : ℝ}
    (hinit : MatchesInitialVelocity u₀ u)
    (hkin : ∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t))
    (hT : 0 ≤ T) :
    finiteInitialKineticEnergy u₀ := by
  rw [finiteInitialKineticEnergy, initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit]
  exact hkin 0 le_rfl hT

/-- Contrapositively, the energy/continuation bridge cannot even be started on
matched data whose initial kinetic energy is infinite on `ℝ^3`. -/
theorem
    not_energyContinuationBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
    {u : NSVelocityField} {u₀ : NSInitialVelocity} {T : ℝ}
    (hfinite : ¬ finiteInitialKineticEnergy u₀)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity u₀ u) :
    ¬ (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t)) := by
  intro hkin
  exact hfinite
    (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_kineticIntegrabilityOnSlab
      hinit hkin hT)

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

/-- On a stationary seed, the finite-time bounded-energy witness slot is exact:
it holds precisely when the initial datum has finite kinetic energy. -/
theorem boundedKineticEnergyUpTo_timeIndependentVelocity_iff
    {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    boundedKineticEnergyUpTo (timeIndependentVelocity u₀) T ↔
      finiteInitialKineticEnergy u₀ := by
  constructor
  · intro hE
    exact
      finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
        (MatchesInitialVelocity_timeIndependentVelocity u₀) hE hT
  · intro hE
    exact boundedKineticEnergyUpTo_timeIndependentVelocity hE

/-- Specializing the stationary-seed bounded-energy criterion to constant
fields, the finite-time bounded-energy slot is inhabited exactly by the zero
field. -/
theorem boundedKineticEnergyUpTo_constantVelocityField_iff
    {T : ℝ} {c : NSSpace}
    (hT : 0 ≤ T) :
    boundedKineticEnergyUpTo (constantVelocityField c) T ↔ c = 0 := by
  constructor
  · intro hE
    by_contra hc
    exact (not_boundedKineticEnergyUpTo_constantVelocityField hc hT) hE
  · intro hc
    subst hc
    simpa [timeIndependentVelocity, constantVelocityField] using
      (boundedKineticEnergyUpTo_timeIndependentVelocity_iff
        (u₀ := (0 : NSInitialVelocity)) (T := T) hT).2
        finiteInitialKineticEnergy_zero

/-- For a stationary seed, the energy/continuation bridge's raw slab
kinetic-integrability input is equivalent to finite initial kinetic energy. -/
theorem kineticIntegrabilityOnSlab_timeIndependentVelocity_iff
    {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity (timeIndependentVelocity u₀) t)) ↔
      finiteInitialKineticEnergy u₀ := by
  constructor
  · intro hkin
    exact
      finiteInitialKineticEnergy_of_matchesInitialVelocity_of_kineticIntegrabilityOnSlab
        (MatchesInitialVelocity_timeIndependentVelocity u₀) hkin hT
  · intro hE t ht0 htT
    simpa [kineticEnergyDensity_timeIndependentVelocity, finiteInitialKineticEnergy] using hE

/-- Specializing the stationary-seed criterion to constant fields, slab
kinetic integrability holds exactly in the zero-field case. -/
theorem kineticIntegrabilityOnSlab_constantVelocityField_iff
    {T : ℝ} {c : NSSpace}
    (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity (constantVelocityField c) t)) ↔
      c = 0 := by
  constructor
  · intro hkin
    by_contra hc
    exact
      (not_energyContinuationBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
        (u := constantVelocityField c)
        (u₀ := constantInitialVelocity c)
        (not_finiteInitialKineticEnergy_constantInitialVelocity hc)
        hT
        (matchesInitialVelocity_constantVelocityField c)) hkin
  · intro hc
    subst hc
    simpa [timeIndependentVelocity, constantVelocityField] using
      (kineticIntegrabilityOnSlab_timeIndependentVelocity_iff
        (u₀ := (0 : NSInitialVelocity)) (T := T) hT).2 finiteInitialKineticEnergy_zero

/-- A nonzero constant velocity field satisfies the corrected coordinate energy
identity, but cannot satisfy the kinetic-integrability input needed to apply
the energy/continuation bridge on any nonnegative slab. -/
theorem
    constantVelocityField_has_coordinateEnergyIdentity_but_not_energyContinuationBridge_kineticIntegrabilityOnSlab
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∀ t,
      HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
        (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T ->
        Integrable (kineticEnergyDensity (constantVelocityField c) t)) := by
  refine ⟨coordinateEnergyDissipationIdentity_smooth_constantVelocityField ν c, ?_⟩
  exact
    not_energyContinuationBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
      (u := constantVelocityField c)
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)
      hT
      (matchesInitialVelocity_constantVelocityField c)

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

/-- Concrete finite-time bounded-energy bridge for bounded two-profile
Schwartz velocity fields with an arbitrary pressure field.  The pressure side
is reduced to the real analytic obligations: pressure-pairing integrability and
zero pressure work.  The velocity class supplies kinetic integrability, viscous
pairing integrability, and nonlinear energy cancellation from the slice-wise
divergence-free hypothesis. -/
theorem boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hpressureIntegrable :
      ∀ t,
        Integrable (pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t))
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    (T : ℝ) :
    boundedKineticEnergyUpTo (fun s y => a s • f y + b s • g y) T := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  change boundedKineticEnergyUpTo u T
  have hbounded : boundedKineticEnergy u := by
    simpa [u] using boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
      a b f g A B haBound hbBound
  rcases hbounded with ⟨_C, _hC_nonneg, henergy⟩
  have hintegrable : EnergyPairingIntegrable u p := by
    intro t
    refine ⟨?_, ?_, ?_⟩
    · simpa [u] using
        integrable_laplacianEnergyPairing_of_schwartzSlice
          (u := u)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · simpa [u] using
        integrable_convectionEnergyPairing_of_schwartzSlice
          (u := u)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · simpa [u] using hpressureIntegrable t
  have hnonlinear :
      ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0 := by
    simpa [u] using
      integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
        a b f g hdiv
  have hkin :
      ∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t) := by
    intro t _ht0 _htT
    exact (henergy t).1
  exact
    boundedKineticEnergyUpTo_of_coordinateEnergyDissipationIdentity_smooth_of_integrable_on_slab
      u p hν
      (by
        simpa [u] using EnergyDerivativeFormula_of_add_scalar_smul_schwartz
          a a' b b' f g ha hb)
      (by
        simpa [u] using heq)
      hintegrable
      (by
        simpa [u] using CoordinateViscousEnergyPairingFormula_of_add_scalar_smul_schwartz
          a b f g)
      (by
        simpa [u] using hboundary)
      hnonlinear
      hkin

/-- Concrete finite-time bounded-energy bridge for bounded two-profile
Schwartz velocity fields with arbitrary time-indexed Schwartz pressure slices.
Here the pressure obligations from
`boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable`
are discharged by spatial Schwartz decay and the divergence-free hypothesis. -/
theorem boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    (T : ℝ) :
    boundedKineticEnergyUpTo (fun s y => a s • f y + b s • g y) T := by
  exact
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B
      (fun s : NSTime => fun y : NSSpace => q s y)
      hν haBound hbBound ha hb heq
      (by
        intro t
        exact
          integrable_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (q := q)
            (hslice := by intro x; rfl))
      (by
        intro t
        exact
          integral_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (q := q)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv T

/-- Concrete finite-time regularity witness constructor for the bounded
two-profile Schwartz class with arbitrary time-indexed Schwartz pressure
slices.  The smoothness and initial-match fields are kept explicit, while the
`bounded_energy_on` field is supplied by the corrected energy inequality and
the pressure-slice integration-by-parts theorem. -/
def ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hinit : MatchesInitialVelocity u₀ (fun s y => a s • f y + b s • g y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T where
  velocity := fun s y => a s • f y + b s • g y
  pressure := fun s : NSTime => fun y : NSSpace => q s y
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
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
      a a' b b' f g A B q hν haBound hbBound ha hb heq hdiv T

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
