import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyContinuationBridge

/-!
# Energy Identity to BKM Continuation Bridge

This file composes the corrected energy-identity finite-time witness
constructors with the concrete BKM continuation surface.  The theorems here do
not prove continuation; they package bottom-up energy and vorticity hypotheses
into the exact finite-time witness and BKM-envelope inputs consumed by the
repaired continuation clause.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A corrected coordinatewise energy identity plus explicit BKM envelope data
supplies the finite-time witness needed to apply the repaired BKM continuation
clause.  The bounded-energy witness field is produced by the corrected energy
inequality, so the continuation clause receives a fully structured
`ExplicitFiniteTimeRegularityWitness`. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
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
    (hdiv : ∀ t x, spatialDivergence u t x = 0)
    (hinit : MatchesInitialVelocity u₀ u)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn u T Ω ∧
          integrableVorticityEnvelopeOn Ω T B) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
    ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth
      (ν := ν) (T := T) (u₀ := u₀)
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin
      (le_of_lt hνpos) hdiv hinit
  have hEnvW :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B := by
    simpa [W, ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth]
      using hEnv
  exact hClause hνpos hsmooth hdiv₀ hfinite W hEnvW

/-- A uniform vorticity bound is enough to provide the BKM envelope data in the
previous bridge, via the existing uniform-to-BKM conversion. -/
theorem
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
    {ν T B : ℝ} {u₀ : NSInitialVelocity}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
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
    (hdiv : ∀ t x, spatialDivergence u t x = 0)
    (hinit : MatchesInitialVelocity u₀ u)
    (hω : uniformVorticityBoundUpTo u T B) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hdiv hinit
      (uniformVorticityBoundUpTo_implies_BKMEnvelope (u := u) (T := T) (B := B) hω)

/-- Target-level version of the generic corrected-energy/BKM application.  Once
the repaired finite-energy BKM continuation target is available, a concrete
finite-energy candidate with the corrected energy identity and a uniform
vorticity bound yields the global output directly. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTarget_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
    (hTarget : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T B : ℝ} {u₀ : NSInitialVelocity}
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
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
    (hdiv : ∀ t x, spatialDivergence u t x = 0)
    (hinit : MatchesInitialVelocity u₀ u)
    (hω : uniformVorticityBoundUpTo u T B) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
      (hClause := hTarget ν u₀ T) hνpos hsmooth hdiv₀ hfinite
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hdiv hinit hω

/-- A repaired BKM clause at a shorter horizon can be applied to a corrected
energy-identity witness constructed on a larger slab.  The witness is first
restricted from `T` to `T'`, and the uniform vorticity bound is converted to
BKM envelope data on the shorter slab. -/
theorem
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound_restrict
    {ν T T' B : ℝ} {u₀ : NSInitialVelocity}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T')
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
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
    (hdiv : ∀ t x, spatialDivergence u t x = 0)
    (hinit : MatchesInitialVelocity u₀ u)
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
    ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth
      (ν := ν) (T := T) (u₀ := u₀)
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin
      (le_of_lt hνpos) hdiv hinit
  have hEnvW :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
          integrableVorticityEnvelopeOn Ω T' Bint := by
    simpa [W, ExplicitFiniteTimeRegularityWitness.restrict,
      ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth]
      using
        (uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
          (u := u) (T := T) (T' := T') (B := B) hω hT)
  exact hClause hνpos hsmooth hdiv₀ hfinite (W.restrict hT) hEnvW

/-- Concrete repaired-BKM application for the bounded two-profile Schwartz
velocity class with affine plus localized Schwartz pressure.  The energy bridge
supplies the finite-time bounded-energy witness, while the supplied uniform
vorticity bound is converted into BKM envelope data. -/
theorem
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T K : ℝ}
    {u₀ : NSInitialVelocity}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure
        ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
          fun s : NSTime => fun y : NSSpace => ρ s * q y))
    (hinit : MatchesInitialVelocity u₀ (fun s y => a s • f y + b s • g y))
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
    (hω : uniformVorticityBoundUpTo (fun s y => a s • f y + b s • g y) T K) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
    ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q hu hp hinit (le_of_lt hνpos)
      haBound hbBound ha hb heq hdiv
  have hEnvW :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    simpa [W,
      ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure]
      using
        (uniformVorticityBoundUpTo_implies_BKMEnvelope
          (u := fun s y => a s • f y + b s • g y) (T := T) (B := K) hω)
  exact hClause hνpos hsmooth hdiv₀ hfinite W hEnvW

/-- Target-level concrete repaired-BKM application for the bounded two-profile
Schwartz velocity class with affine plus localized Schwartz pressure. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTarget_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound
    (hTarget : ExplicitFiniteEnergyBKMContinuationTarget)
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T K : ℝ}
    {u₀ : NSInitialVelocity}
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure
        ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
          fun s : NSTime => fun y : NSSpace => ρ s * q y))
    (hinit : MatchesInitialVelocity u₀ (fun s y => a s • f y + b s • g y))
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
    (hω : uniformVorticityBoundUpTo (fun s y => a s • f y + b s • g y) T K) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound
      a a' b b' f g A B c π ρ q
      (hClause := hTarget ν u₀ T) hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv hω

/-- Restricted-horizon concrete repaired-BKM application for the bounded
two-profile Schwartz velocity class with affine plus localized Schwartz
pressure.  The finite-time witness is built on `0 ≤ t ≤ T`, then restricted to
the shorter BKM horizon `T'`. -/
theorem
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound_restrict
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T T' K : ℝ}
    {u₀ : NSInitialVelocity}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T')
    (hνpos : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv₀ : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure
        ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
          fun s : NSTime => fun y : NSSpace => ρ s * q y))
    (hinit : MatchesInitialVelocity u₀ (fun s y => a s • f y + b s • g y))
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
    (hω : uniformVorticityBoundUpTo (fun s y => a s • f y + b s • g y) T K)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
    ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q hu hp hinit (le_of_lt hνpos)
      haBound hbBound ha hb heq hdiv
  have hEnvW :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
          integrableVorticityEnvelopeOn Ω T' Bint := by
    simpa [W, ExplicitFiniteTimeRegularityWitness.restrict,
      ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure]
      using
        (uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
          (u := fun s y => a s • f y + b s • g y) (T := T) (T' := T') (B := K) hω hT)
  exact hClause hνpos hsmooth hdiv₀ hfinite (W.restrict hT) hEnvW

/-- Actual zero-data global regularity obtained through the corrected
energy/BKM bridge route.  This deliberately uses the bridge hypotheses for the
zero velocity and pressure fields, rather than calling the direct zero global
output theorem.  It is a sanity theorem for the composed route, not a new
general continuation result. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_via_energy_BKMBridge
    {ν : ℝ}
    (hνpos : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv₀ : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
      (ν := ν) (T := 0) (B := 0) (u₀ := (0 : NSInitialVelocity))
      (hClause := ExplicitFiniteEnergyBKMContinuationClause_zero ν 0)
      hνpos
      smoothInitialVelocityData_zero
      hdiv₀
      finiteInitialKineticEnergy_zero
      (0 : NSVelocityField)
      (0 : NSPressureField)
      (by
        simpa [zeroFiniteTimeRegularityWitness] using
          (zeroFiniteTimeRegularityWitness ν 0).smooth_velocity)
      (by
        simpa [zeroFiniteTimeRegularityWitness] using
          (zeroFiniteTimeRegularityWitness ν 0).smooth_pressure)
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      CoordinateViscousEnergyPairingFormula_zero
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)
      (by
        intro t _ht0 _htT
        exact (meaningfulCoordinateEnergyDissipationIdentity_smooth_zero ν t).1)
      (by
        intro t x
        simpa using (spatialDivergence_zero t x))
      (by
        intro x
        rfl)
      (by
        simpa using (uniformVorticityBoundUpTo_zero 0))

/-- The kinetic-energy integrability input of the energy/BKM bridge rules out
every field matching nonzero constant initial data, already at time `0`. -/
theorem not_energyBKMBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t)) := by
  intro hkin
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
      (u := u) hc hinit (hkin 0 le_rfl hT)

/-- A nonzero constant velocity field satisfies the corrected coordinate energy
identity and has an explicit BKM envelope, but it cannot satisfy the kinetic
integrability input needed to construct an energy/BKM finite-time witness. -/
theorem
    constantVelocityField_has_energyIdentity_and_BKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∀ t,
      HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
        (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn (constantVelocityField c) T Ω ∧
          integrableVorticityEnvelopeOn Ω T B) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity (constantVelocityField c) t)) := by
  refine ⟨coordinateEnergyDissipationIdentity_smooth_constantVelocityField ν c, ?_, ?_⟩
  · exact ⟨fun _ : NSTime => 0, 0, constantVelocityField_has_constantBKMEnvelope c T hT⟩
  · exact
      not_energyBKMBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_constantInitialVelocity
        (u := constantVelocityField c) hc hT (matchesInitialVelocity_constantVelocityField c)

/-- The kinetic-energy integrability input of the energy/BKM bridge also rules
out every field matching nontrivial heat-shear initial data at time `0`. -/
theorem not_energyBKMBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t)) := by
  intro hkin
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
      (u := u) ha hk hinit (hkin 0 le_rfl hT)

/-- A nontrivial heat-shear candidate can carry an explicit BKM envelope on a
nonnegative-viscosity slab, but the same time-zero finite-energy obstruction
prevents it from entering the energy/BKM bridge. -/
theorem heatShearVelocityField_has_BKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
    {ν a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (heatShearVelocityField ν a k) T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity (heatShearVelocityField ν a k) t)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ : NSTime => |a * k|, T * |a * k|,
      heatShearVelocityField_has_constantBKMEnvelope ν a k T hν hT⟩
  · exact
      not_energyBKMBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_heatShearInitialVelocity
        (u := heatShearVelocityField ν a k) ha hk hT
        (matchesInitialVelocity_heatShearVelocityField ν a k)

end NavierStokes
end FluidDynamics
end Mettapedia
