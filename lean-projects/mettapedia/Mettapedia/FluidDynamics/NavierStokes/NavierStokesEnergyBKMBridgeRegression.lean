import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBKMBridge

/-!
# Navier-Stokes Energy/BKM Bridge Regression

Small theorem-level checks for the bridge that packages corrected energy
identity hypotheses and vorticity control into the repaired BKM continuation
surface.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesEnergyBKMBridgeRegression

theorem generic_energy_identity_uniform_vorticity_applies_repaired_BKM_regression
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
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hdiv hinit hω

theorem generic_energy_identity_uniform_vorticity_applies_repaired_BKM_target_regression
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
    ExplicitFiniteEnergyBKMContinuationTarget_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound
      hTarget hνpos hsmooth hdiv₀ hfinite
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hdiv hinit hω

theorem generic_energy_identity_uniform_vorticity_applies_repaired_BKM_restrict_regression
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
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_coordinateEnergyDissipationIdentity_smooth_of_uniformVorticityBound_restrict
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hdiv hinit hω hT

theorem affine_plus_schwartz_energy_uniform_vorticity_applies_repaired_BKM_regression
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
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound
      a a' b b' f g A B c π ρ q
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv hω

theorem affine_plus_schwartz_energy_uniform_vorticity_applies_repaired_BKM_target_regression
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
    ExplicitFiniteEnergyBKMContinuationTarget_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound
      hTarget a a' b b' f g A B c π ρ q
      hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv hω

theorem affine_plus_schwartz_energy_uniform_vorticity_applies_repaired_BKM_restrict_regression
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
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_of_uniformVorticityBound_restrict
      a a' b b' f g A B c π ρ q
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv hω hT

theorem affine_plus_schwartz_energy_internal_vorticity_applies_repaired_BKM_regression
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
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
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv

theorem affine_plus_schwartz_energy_internal_vorticity_applies_repaired_BKM_target_regression
    (hTarget : ExplicitFiniteEnergyBKMContinuationTarget)
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
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
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      (T := T) hTarget a a' b b' f g A B c π ρ q
      hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv

theorem affine_plus_schwartz_energy_internal_vorticity_applies_repaired_BKM_restrict_regression
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T T' : ℝ}
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
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure_restrict
      a a' b b' f g A B c π ρ q
      (hClause := hClause) hνpos hsmooth hdiv₀ hfinite
      hu hp hinit haBound hbBound ha hb heq hdiv hT

theorem zero_global_output_via_energy_BKM_bridge_regression
    {ν : ℝ}
    (hνpos : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesGlobalOutput_zero_via_energy_BKMBridge hνpos

theorem nonzero_constant_energy_BKM_bridge_kinetic_integrability_obstruction_regression
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
  exact
    constantVelocityField_has_energyIdentity_and_BKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
      (ν := ν) (T := T) hc hT

theorem nontrivial_heat_shear_energy_BKM_bridge_kinetic_integrability_obstruction_regression
    {ν a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (heatShearVelocityField ν a k) T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity (heatShearVelocityField ν a k) t)) := by
  exact
    heatShearVelocityField_has_BKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
      (ν := ν) (a := a) (k := k) (T := T) ha hk hν hT

theorem nontrivial_heat_shear_exp_BKM_bridge_kinetic_integrability_obstruction_regression
    {ν a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    (vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|)) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity (heatShearVelocityField ν a k) t)) := by
  exact
    heatShearVelocityField_has_expBKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
      (ν := ν) (a := a) (k := k) (T := T) ha hk hν hT

theorem transported_full_drift_heat_shear_energy_BKM_bridge_kinetic_integrability_obstruction_regression
    {ν T : ℝ}
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν 1 1 1 1 1) T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity (heatShearTransportFullDriftVelocityField ν 1 1 1 1 1) t)) := by
  exact
    heatShearTransportFullDriftVelocityField_has_BKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (T := T)
      one_ne_zero hν hT

theorem transported_full_drift_heat_shear_exp_BKM_bridge_kinetic_integrability_obstruction_regression
    {ν T : ℝ}
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    (vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν 1 1 1 1 1) T
        (heatShearExpVorticityEnvelope ν 1 1) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν 1 1) T (T * |(1 : ℝ) * 1|)) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T →
        Integrable (kineticEnergyDensity
          (heatShearTransportFullDriftVelocityField ν 1 1 1 1 1) t)) := by
  exact
    heatShearTransportFullDriftVelocityField_has_expBKMEnvelope_but_not_energyBKMBridge_kineticIntegrabilityOnSlab
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (T := T)
      one_ne_zero hν hT

theorem generic_nonfinite_energy_initial_data_blocks_energy_BKM_bridge_regression
    {T : ℝ}
    (hT : 0 ≤ T) :
    ¬ (∀ t, 0 ≤ t → t ≤ T →
      Integrable
        (kineticEnergyDensity (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t)) := by
  exact
    not_energyBKMBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
      (u := heatShearTransportFullDriftVelocityField 1 1 1 1 1 1)
      (u₀ := heatShearTransportFullDriftInitialVelocity 1 1 1 1 1)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity one_ne_zero)
      hT
      (matchesInitialVelocity_heatShearTransportFullDriftVelocityField 1 1 1 1 1 1)

end NavierStokesEnergyBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
