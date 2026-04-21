import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyInequality

/-!
# Navier-Stokes Energy Inequality Regression

Small theorem-level checks for the concrete `ℝ × ℝ^3` energy-identity lane.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesEnergyInequalityRegression

theorem zero_coordinate_energy_identity_regression
    (ν : ℝ) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
        (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact coordinateEnergyDissipationIdentity_smooth_zero ν

theorem zero_meaningful_coordinate_energy_identity_regression
    (ν : ℝ) :
    ∀ t,
      MeasureTheory.Integrable (kineticEnergyDensity (0 : NSVelocityField) t) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact meaningfulCoordinateEnergyDissipationIdentity_smooth_zero ν

theorem normalized_kinetic_energy_nonnegative_regression
    (u : NSVelocityField) :
    ∀ t, 0 ≤ normalizedKineticEnergy u t := by
  intro t
  exact normalizedKineticEnergy_nonneg u t

theorem coordinate_dissipation_rate_nonnegative_regression
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) :
    ∀ t, 0 ≤ coordinateEnergyDissipationRate u ν t := by
  intro t
  exact coordinateEnergyDissipationRate_nonneg u hν t

theorem coordinate_energy_identity_slope_nonpositive_regression
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) :
    ∀ t, -(coordinateEnergyDissipationRate u ν t) ≤ 0 := by
  intro t
  exact neg_coordinateEnergyDissipationRate_nonpos u hν t

theorem constant_velocity_guard_obstruction_regression
    (ν : ℝ) :
    ∃ c : NSSpace,
      c ≠ 0 ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
          (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      ¬ boundedKineticEnergy (constantVelocityField c) := by
  exact exists_nonzero_constantVelocityField_coordinateEnergyIdentity_without_boundedEnergy ν

theorem scalar_schwartz_pressure_smooth_regression
    {ρ : NSTime → ℝ} (hρ : ContDiff ℝ ∞ ρ) (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  exact smoothSpaceTimePressure_scalar_smul_schwartzPressure hρ q

theorem affine_pressure_smooth_regression
    {c : NSTime → NSSpace} {π : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) := by
  exact smoothSpaceTimePressure_affinePressure hc hπ

theorem affine_plus_schwartz_pressure_smooth_regression
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure
      ((fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) +
        fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  exact smoothSpaceTimePressure_affine_add_scalar_smul_schwartzPressure hc hπ hρ q

theorem affine_plus_schwartz_pressure_energy_identity_regression
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (ν : ℝ)
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
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q ν haBound hbBound ha hb heq hdiv

theorem affine_plus_schwartz_pressure_energy_antitone_regression
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
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    Antitone (normalizedKineticEnergy (fun s y => a s • f y + b s • g y)) := by
  exact
    normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv

theorem affine_plus_schwartz_pressure_energy_two_time_bound_regression
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
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ∧
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ≤
        normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₀ := by
  exact
    normalizedKineticEnergy_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv ht

theorem affine_plus_schwartz_pressure_kinetic_energy_two_time_bound_regression
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
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ∧
      kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ≤
        kineticEnergyAt (fun s y => a s • f y + b s • g y) t₀ := by
  exact
    kineticEnergyAt_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv ht

end NavierStokesEnergyInequalityRegression
end NavierStokes
end FluidDynamics
end Mettapedia
