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

end NavierStokesEnergyContinuationBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
