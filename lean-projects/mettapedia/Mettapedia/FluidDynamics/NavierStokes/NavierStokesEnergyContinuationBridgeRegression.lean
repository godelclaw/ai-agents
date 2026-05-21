import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyContinuationBridge

/-!
# Navier-Stokes Energy/Continuation Bridge Regression

Small theorem-level checks for the bridge from the corrected energy inequality
to the finite-time bounded-energy predicate used by continuation witnesses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesEnergyContinuationBridgeRegression

theorem generic_energy_identity_supplies_bounded_energy_up_to_regression
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
  exact
    boundedKineticEnergyUpTo_of_coordinateEnergyDissipationIdentity_smooth_of_integrable_on_slab
      u p hν hderiv heq hintegrable hviscous hboundary hnonlinear hkin

theorem generic_energy_identity_supplies_finite_time_witness_velocity_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_coordinateEnergyDissipationIdentity_smooth
      (ν := ν) (T := T) (u₀ := u₀)
      u p hu hp hderiv heq hintegrable hviscous hboundary hnonlinear hkin hν hdiv hinit).velocity =
      u := by
  rfl

theorem pressure_integrable_two_profile_bounded_energy_up_to_regression
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
  exact
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B p hν haBound hbBound ha hb heq
      hpressureIntegrable hboundary hdiv T

theorem schwartz_pressure_slice_two_profile_bounded_energy_up_to_regression
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
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
      a a' b b' f g A B q hν haBound hbBound ha hb heq hdiv T

theorem schwartz_pressure_slice_two_profile_finite_time_witness_pressure_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B q hu hp hinit hν haBound hbBound ha hb heq hdiv).pressure =
      (fun s : NSTime => fun y : NSSpace => q s y) := by
  rfl

theorem affine_plus_schwartz_pressure_bounded_energy_up_to_regression
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
              (fun s : NSTime => fun y : NSSpace => ρ s * q y)) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    (T : ℝ) :
    boundedKineticEnergyUpTo (fun s y => a s • f y + b s • g y) T := by
  exact
    boundedKineticEnergyUpTo_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv T

theorem affine_plus_schwartz_pressure_finite_time_witness_pressure_regression
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu :
      smoothSpaceTimeVelocity (fun s y => a s • f y + b s • g y))
    (hp :
      smoothSpaceTimePressure
        ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
          (fun s : NSTime => fun y : NSSpace => ρ s * q y)))
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
              (fun s : NSTime => fun y : NSSpace => ρ s * q y)) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    (ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q hu hp hinit hν haBound hbBound ha hb heq hdiv).pressure =
      ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
        (fun s : NSTime => fun y : NSSpace => ρ s * q y)) := by
  rfl

theorem nonzero_constant_field_energy_continuation_bridge_kinetic_integrability_obstruction_regression
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∀ t,
      HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
        (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      ¬ (∀ t, 0 ≤ t → t ≤ T ->
        Integrable (kineticEnergyDensity (constantVelocityField c) t)) := by
  exact
    constantVelocityField_has_coordinateEnergyIdentity_but_not_energyContinuationBridge_kineticIntegrabilityOnSlab
      (ν := ν) (T := T) hc hT

theorem time_independent_velocity_bounded_energy_up_to_iff_regression
    {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    boundedKineticEnergyUpTo (timeIndependentVelocity u₀) T ↔
      finiteInitialKineticEnergy u₀ := by
  exact boundedKineticEnergyUpTo_timeIndependentVelocity_iff hT

theorem constant_velocity_field_bounded_energy_up_to_iff_zero_regression
    {T : ℝ} {c : NSSpace}
    (hT : 0 ≤ T) :
    boundedKineticEnergyUpTo (constantVelocityField c) T ↔ c = 0 := by
  exact boundedKineticEnergyUpTo_constantVelocityField_iff hT

theorem time_independent_velocity_energy_continuation_bridge_kinetic_integrability_iff_regression
    {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity (timeIndependentVelocity u₀) t)) ↔
      finiteInitialKineticEnergy u₀ := by
  exact kineticIntegrabilityOnSlab_timeIndependentVelocity_iff hT

theorem constant_velocity_field_energy_continuation_bridge_kinetic_integrability_iff_zero_regression
    {T : ℝ} {c : NSSpace}
    (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity (constantVelocityField c) t)) ↔
      c = 0 := by
  exact kineticIntegrabilityOnSlab_constantVelocityField_iff hT

theorem generic_nonfinite_initial_energy_blocks_energy_continuation_bridge_regression
    {T : ℝ}
    (hT : 0 ≤ T) :
    ¬ (∀ t, 0 ≤ t → t ≤ T →
      Integrable
        (kineticEnergyDensity (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t)) := by
  exact
    not_energyContinuationBridge_kineticIntegrabilityOnSlab_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
      (u := heatShearTransportFullDriftVelocityField 1 1 1 1 1 1)
      (u₀ := heatShearTransportFullDriftInitialVelocity 1 1 1 1 1)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity one_ne_zero)
      hT
      (matchesInitialVelocity_heatShearTransportFullDriftVelocityField 1 1 1 1 1 1)

end NavierStokesEnergyContinuationBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
