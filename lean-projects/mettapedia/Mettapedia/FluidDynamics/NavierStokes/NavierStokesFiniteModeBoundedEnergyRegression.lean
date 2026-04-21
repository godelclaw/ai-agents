import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergy

/-!
# Navier-Stokes Finite-Mode Bounded-Energy Regression

Regression checks for the positive bounded-energy two-mode Schwartz finite-mode
construction.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeBoundedEnergyRegression

theorem two_mode_schwartz_initial_finite_energy_regression
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    finiteInitialKineticEnergy (twoModeSchwartzInitialVelocity a0 b0 f g) := by
  exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity a0 b0 f g

theorem two_mode_schwartz_matches_initial_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) :
    MatchesInitialVelocity
      (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (twoModeSchwartzVelocity a b f g) := by
  exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g

theorem two_mode_schwartz_bounded_energy_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergy (twoModeSchwartzVelocity a b f g) := by
  exact
    boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
      a b f g A B haBound hbBound

theorem two_mode_schwartz_bounded_energy_up_to_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  exact
    boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
      a b f g A B T haBound hbBound

theorem two_mode_schwartz_smooth_velocity_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) := by
  exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g

theorem two_mode_schwartz_time_derivative_deriv_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x =
        deriv a t • f x + deriv b t • g x := by
  exact timeVelocityDerivative_twoModeSchwartzVelocity_deriv ha hb f g

theorem two_mode_schwartz_spatial_laplacian_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (twoModeSchwartzVelocity a b f g) t x =
      a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  exact spatialLaplacian_twoModeSchwartzVelocity a b f g t x

theorem two_mode_schwartz_spatial_convection_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialConvection (twoModeSchwartzVelocity a b f g) t x =
      (a t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
        (b t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  exact spatialConvection_twoModeSchwartzVelocity a b f g t x

theorem two_mode_schwartz_momentum_explicit_closure_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
      deriv a t • f x + deriv b t • g x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              (b t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x) +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x := by
  exact
    momentumEquation_twoModeSchwartzVelocity_of_explicitClosure
      ha hb ν c π ρ f g q hclosure

theorem one_one_two_mode_schwartz_momentum_explicit_closure_regression
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact momentumEquation_oneOneTwoModeSchwartzVelocity_of_explicitClosure
    ν c π ρ f g q hclosure

theorem one_one_two_mode_schwartz_inviscid_zero_pressure_momentum_regression
    (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (0 : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    momentumEquation_oneOneTwoModeSchwartzVelocity_inviscid_zeroPressure_of_convectionClosure
      f g hclosure

theorem one_one_two_mode_schwartz_velocity_nonzero_regression
    (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0) :
    ∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace) := by
  exact oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg

theorem zero_amplitude_two_mode_schwartz_velocity_regression
    (f g : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g =
      (0 : NSVelocityField) := by
  exact twoModeSchwartzVelocity_zero_zero f g

theorem affine_add_scalar_schwartz_pressure_smooth_regression
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) := by
  exact smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q

theorem affine_add_scalar_schwartz_pressure_time_only_regression
    (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) :
    affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
        (fun _ : NSTime => 0) q =
      fun t : NSTime => fun _ : NSSpace => π t := by
  exact affineAddScalarSchwartzPressure_zero_timeOnly π q

theorem zero_amplitude_two_mode_schwartz_momentum_regression
    (ν : ℝ) (π : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x := by
  exact momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure ν π f g q

theorem unit_bump_schwartz_velocity_nonzero_regression :
    ∃ x : NSSpace, nsUnitBumpSchwartzVelocity x ≠ 0 := by
  exact nsUnitBumpSchwartzVelocity_nonzero

theorem one_one_antiprofile_schwartz_velocity_zero_regression
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) =
      (0 : NSVelocityField) := by
  exact oneOneAntiProfileSchwartzVelocity_zero f

theorem one_one_antiprofile_schwartz_initial_zero_regression
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzInitialVelocity 1 1 f (-f) =
      (0 : NSInitialVelocity) := by
  exact oneOneAntiProfileSchwartzInitialVelocity_zero f

theorem one_one_antiprofile_full_viscous_momentum_regression
    {ν : ℝ} (hν : 0 < ν) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x := by
  exact
    momentumEquation_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
      hν π f q

theorem one_one_antiprofile_full_viscous_zero_pressure_closure_regression
    {ν : ℝ} (hν : 0 < ν) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  exact explicitClosure_oneOneAntiProfileSchwartzVelocity_zeroPressure_of_posViscosity hν f

theorem exists_nonzero_profiles_pressure_full_viscous_closure_regression
    {ν : ℝ} (hν : 0 < ν) :
    ∃ f g : NSSchwartzInitialVelocity, ∃ p : NSPressureField,
      (∃ x : NSSpace, f x ≠ 0) ∧
      (∃ x : NSSpace, g x ≠ 0) ∧
      (∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) := by
  exact exists_nonzeroSchwartzProfiles_pressure_explicitClosure_fullViscousNS_of_posViscosity hν

theorem two_mode_schwartz_spatial_divergence_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialDivergence (twoModeSchwartzVelocity a b f g) t x =
      a t * initialSpatialDivergence (f : NSInitialVelocity) x +
        b t * initialSpatialDivergence (g : NSInitialVelocity) x := by
  exact spatialDivergence_twoModeSchwartzVelocity a b f g t x

theorem two_mode_schwartz_spatial_divergence_zero_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    ∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0 := by
  exact spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv

theorem two_mode_schwartz_positive_package_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  exact
    twoModeSchwartzVelocity_finiteInitial_matches_boundedEnergyUpTo_of_abs_le
      a b f g A B T haBound hbBound

theorem two_mode_schwartz_positive_smooth_package_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  exact
    twoModeSchwartzVelocity_finiteInitial_smooth_matches_boundedEnergyUpTo_of_abs_le
      ha hb f g A B T haBound hbBound

theorem two_mode_schwartz_positive_smooth_divergence_free_package_regression
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      (∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  exact
    twoModeSchwartzVelocity_finiteInitial_smooth_matches_divergenceFree_boundedEnergyUpTo_of_abs_le
      ha hb f g A B T haBound hbBound hfDiv hgDiv

def one_one_two_mode_schwartz_inviscid_zero_pressure_witness_regression
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ExplicitFiniteTimeRegularityWitness 0
      (twoModeSchwartzInitialVelocity 1 1 f g) T := by
  exact
    ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
      f g hfDiv hgDiv hclosure

theorem one_one_two_mode_schwartz_nonzero_inviscid_witness_regression
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
      Nonempty
        (ExplicitFiniteTimeRegularityWitness 0
          (twoModeSchwartzInitialVelocity 1 1 f g) T) := by
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidWitness_of_convectionClosure
      f g hfg hfDiv hgDiv hclosure

theorem two_mode_schwartz_finite_time_witness_velocity_regression
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu : smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g))
    (hp : smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q))
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q hu hp hinit hν haBound hbBound ha hb heq hdiv).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_smooth_coefficients_witness_velocity_regression
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν
      haBound hbBound ha hb heq hdiv).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_smooth_coefficients_witness_pressure_regression
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν
      haBound hbBound ha hb heq hdiv).pressure =
      affineAddScalarSchwartzPressure c π ρ q := by
  rfl

theorem two_mode_schwartz_smooth_divergence_free_witness_velocity_regression
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hinit hν
      haBound hbBound ha hb heq).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_canonical_initial_witness_velocity_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (ν := ν) (T := T)
      a b f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hν
      haBound hbBound heq).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_canonical_initial_witness_pressure_regression
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (ν := ν) (T := T)
      a b f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hν
      haBound hbBound heq).pressure =
      affineAddScalarSchwartzPressure c π ρ q := by
  rfl

end NavierStokesFiniteModeBoundedEnergyRegression
end NavierStokes
end FluidDynamics
end Mettapedia
