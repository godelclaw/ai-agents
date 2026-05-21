import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge

/-!
# Regression Tests for the Finite-Mode Schwartz BKM Bridge
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem two_mode_schwartz_divergence_free_zero_bridge_finite_time_witness_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        W.velocity =
            twoModeSchwartzVelocity
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => 0)
              (fun _ : NSTime => 0)
              (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))

theorem two_mode_schwartz_divergence_free_zero_bridge_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  have hω :
      uniformVorticityBoundUpTo
        (twoModeSchwartzVelocity
          (fun _ : NSTime => 0) (fun _ : NSTime => 0)
          (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
        0 0 := by
    simpa [twoModeSchwartzVelocity_zero_zero] using
      (uniformVorticityBoundUpTo_zero 0)
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_and_uniformVorticityBound
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (K := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))
      hω

theorem two_mode_schwartz_divergence_free_zero_bridge_internal_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))

theorem one_one_two_mode_schwartz_nonzero_inviscid_zero_pressure_BKM_premise_regression
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
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
      f g hfg hfDiv hgDiv hclosure

theorem one_one_two_mode_schwartz_nonzero_pos_viscosity_pressure_repaired_BKM_premise_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hpressure : ∀ t x,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_posViscosity_BKMPremise_of_inviscidClosure_pressureGradient
      hν f g c π ρ q hc hπ hρ hfg hfDiv hgDiv hclosure hpressure

theorem one_one_two_mode_affine_pressure_lapSum_pair_mismatch_obstruction_regression
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          ρ t •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure hbad

theorem one_one_two_mode_affine_pressure_zero_localized_amplitude_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        ρ t = 0 ∧
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_zeroLocalizedAmplitude_lapSum_pair_ne
      hν f g c π ρ q hclosure hbad

theorem one_one_two_mode_affine_pressure_no_scalar_lapSum_pair_fit_obstruction_regression
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t, ∀ r : ℝ, ∃ x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          r •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure hbad

theorem one_one_two_mode_affine_pressure_same_pressureGradient_pair_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
        ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne
      hν f g q hclosure hbad

theorem one_one_two_mode_inviscid_BKM_and_pos_viscosity_affine_pressure_BKM_data_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
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
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
        ∃ W : ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_inviscidBKM_and_not_exists_posViscosity_BKMData_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hfg hfDiv hgDiv hclosure hbad

theorem one_one_two_mode_affine_pressure_repeated_gradient_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y ∧
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_pressureGradient_pair_eq_lapSum_pair_ne
      hν f g q hclosure hbad

theorem two_mode_schwartz_divergence_free_zero_bridge_schwartz_pressure_slice_witness_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        W.velocity =
            twoModeSchwartzVelocity
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace => (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa [twoModeSchwartzVelocity_zero_zero] using
          momentumEquation_zeroVelocityField_timeOnlyPressure 0 (fun _ : NSTime => 0) t x)

theorem two_mode_schwartz_divergence_free_zero_bridge_schwartz_pressure_slice_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa [twoModeSchwartzVelocity_zero_zero] using
          momentumEquation_zeroVelocityField_timeOnlyPressure 0 (fun _ : NSTime => 0) t x)

theorem two_mode_schwartz_divergence_free_zero_bridge_explicitClosure_schwartz_pressure_slice_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa using spatialPressureGradient_zero t x)

theorem one_one_antiprofile_schwartz_pressure_slice_zero_BKM_premise_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_oneOneAntiProfile_schwartzPressureSlice_zeroPressure
      (ν := 0)
      (T := 0)
      le_rfl
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_premise_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_zero_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_zero_envelope_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_canonical_zero_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W = zeroFiniteTimeRegularityWitness 0 0 ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
          vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_canonicalZeroWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_affine_time_only_pressure_BKM_zero_envelope_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0)
            (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => 0)
            (0 : 𝓢(NSSpace, ℝ)) ∧
        vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
      (a := fun _ : NSTime => 0)
      (A := 0)
      (π := fun _ : NSTime => (1 : ℝ))
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_affine_time_only_pressure_BKM_canonical_gauge_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W =
          (zeroFiniteTimeRegularityWitness 0 0).addTimeOnlyPressure
            (fun _ : NSTime => (1 : ℝ))
            (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ))) ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0)
              (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_canonicalGaugeWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (π := fun _ : NSTime => (1 : ℝ))
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem zero_velocity_BKM_data_nonzero_spatial_affine_pressure_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeffOn
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      ?_
  refine ⟨0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_spatial_affine_pressure_exact_classification_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧ ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  exact
    BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
      c π q hc hπ

theorem zero_velocity_BKM_data_spatial_affine_pressure_zero_coeff_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_spatialAffinePressure_of_affineCoeff_zeroOn
      (ν := ν)
      (T := T)
      (fun _ : NSTime => 0)
      π q
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      hπ
      (by intro t _ht0 _htT; rfl)

theorem zero_velocity_BKM_data_spatial_affine_pressure_nonzero_initial_or_coeff_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_initialVelocity_ne_zero_or_exists_nonzeroAffineCoeffOn
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (contDiff_const :
        ContDiff ℝ ∞ (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      ?_
  refine Or.inr ?_
  refine ⟨0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem spatial_pressure_gradient_scalar_schwartz_pressure_regression
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
      ρ t • spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  exact spatialPressureGradient_scalarSchwartzPressure ρ q t x

theorem spatial_pressure_gradient_affine_add_scalar_schwartz_pressure_regression
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
      c t + ρ t •
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  exact spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_exact_balance_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
      c π ρ q hc hπ hρ

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_balanced_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_pressureGradientBalanceOn
      (ν := ν)
      (T := T)
      (fun _ : NSTime => 0)
      π
      (fun _ : NSTime => 0)
      q
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      hπ
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (by intro t x _ht0 _htT; simp)

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_balance_failure_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_pressureGradientBalanceFailureOn
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (contDiff_const :
        ContDiff ℝ ∞ (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      ?_
  refine Or.inr ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    simpa [nsCoord0] using congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonconstant_gradient_impossible_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, ∃ y, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0 ∧
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x ≠
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  exact
    not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_nonconstant_schwartzPressureGradientOn
      c π ρ q hc hπ hρ hfail

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_constant_gradient_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem schwartz_map_constant_gradient_zero_regression
    (q : 𝓢(NSSpace, ℝ))
    (hconst : ∀ x : NSSpace,
      gradient (fun z : NSSpace => q z) x =
        gradient (fun z : NSSpace => q z) (0 : NSSpace)) :
    ∀ x : NSSpace, gradient (fun z : NSSpace => q z) x = 0 := by
  exact schwartzMap_gradient_constant_eq_zero q hconst

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_zero_gradient_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_affine_coeff_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 → c t = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_exact_collapsed_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      c π ρ q hc hπ hρ

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_momentum_exact_collapsed_regression
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      (∀ t, c t = 0) ∧
        ((∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
      a ν c π ρ f q

theorem equal_amplitude_antiprofile_arbitrary_pressure_momentum_exact_regression
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      a ν f p

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_BKM_exact_collapsed_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_BKM_data_iff_zero_velocity_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p

theorem equal_amplitude_antiprofile_BKM_data_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      a f hp

theorem equal_amplitude_antiprofile_BKM_data_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem equal_amplitude_antiprofile_initial_full_affine_localized_pressure_BKM_exact_collapsed_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_initial_BKM_data_iff_zero_velocity_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity a f p

theorem equal_amplitude_antiprofile_initial_BKM_data_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
      a f hp

theorem equal_amplitude_antiprofile_initial_BKM_data_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_zero_but_antiprofile_arbitrary_pressure_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_antiprofile_initial_but_arbitrary_pressure_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_zero_and_antiprofile_arbitrary_pressure_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

theorem finite_energy_BKM_clause_zero_and_antiprofile_full_affine_localized_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      (ν := ν) (T := T) a c π ρ f q hc hπ hρ

theorem finite_energy_BKM_clause_antiprofile_initial_and_full_affine_localized_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      (ν := ν) (T := T) a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_BKM_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem equal_amplitude_antiprofile_initial_full_affine_localized_pressure_BKM_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_zero_but_antiprofile_full_affine_localized_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_matching_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_momentum_equation_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hbad :
      (∃ t, c t ≠ 0) ∨
        ((∃ t, ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_arbitrary_pressure_momentum_equation_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f p hbad

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_momentum_equation_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f p

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_BKM_data_and_momentum_equation_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

theorem finite_time_witness_antiprofile_initial_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero_on
      (ν := ν) (T := T) a f hp

theorem finite_time_witness_antiprofile_initial_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hbad :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero_on
      (ν := ν) (T := T) a f hbad

theorem finite_time_witness_antiprofile_initial_internal_pressure_zero_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient W.pressure t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
      a f W hWvel

theorem finite_time_witness_antiprofile_initial_zero_BKM_envelope_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
      a f W hWvel

theorem BKM_data_antiprofile_initial_zero_vorticity_envelope_zero_budget_normal_form_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVorticityEnvelope_zeroBudget
      a f p

theorem finite_time_witness_antiprofile_initial_internal_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient W.pressure t x ≠ 0 := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_of_exists_pressure_spatialPressureGradient_ne_zero_on
      a f

theorem zero_velocity_BKM_data_pressure_gradient_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData

theorem zero_velocity_BKM_data_initial_velocity_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 := by
  exact BKMData_zeroVelocity_implies_initialVelocity_zero hData

theorem zero_velocity_BKM_data_initial_velocity_and_pressure_gradient_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 ∧
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
      hData

theorem zero_velocity_BKM_data_exact_classification_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
      hp

theorem zero_velocity_BKM_data_time_only_pressure_iff_initial_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 := by
  exact
    BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      π hπ

theorem zero_velocity_BKM_data_time_only_pressure_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_timeOnlyPressure (ν := ν) (T := T) π hπ

theorem zero_velocity_BKM_data_time_only_pressure_nonzero_initial_impossible_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  exact
    not_exists_BKMData_zeroVelocity_timeOnlyPressure_of_initialVelocity_ne_zero
      π hπ hu0

theorem zero_velocity_BKM_data_nonzero_initial_velocity_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (p := (0 : NSPressureField))
      ?_
  intro hzero
  have hpoint :
      (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
          (0 : NSSpace) =
        (0 : NSInitialVelocity) (0 : NSSpace) := by
    exact congrFun hzero (0 : NSSpace)
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hpoint
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_nonzero_initial_or_pressure_gradient_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero_or_exists_spatialPressureGradient_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (p := fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0)
      ?_
  refine Or.inr ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  rw [spatialPressureGradient_coord0Linear]
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_nonzero_pressure_gradient_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (p := fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0)
      ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  rw [spatialPressureGradient_coord0Linear]
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
