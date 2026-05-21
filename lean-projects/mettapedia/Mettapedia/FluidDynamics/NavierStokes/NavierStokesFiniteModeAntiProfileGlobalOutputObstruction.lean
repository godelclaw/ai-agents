import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction

/-!
# Finite-Mode Anti-Profile Global-Output Obstructions

This file pushes the cancelled equal-amplitude anti-profile branch onto the
exact whole-space output surface with the pressure fixed in advance.

Because the anti-profile velocity collapses to zero, the exact global-output
question becomes a pure pressure audit: an arbitrary pressure works exactly when
its spatial gradient vanishes everywhere, and the affine-plus-localized
Schwartz subclass collapses to the already-classified zero-flow conditions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Exact whole-space outputs with zero initial datum, zero velocity, and a
fixed pressure exist exactly when that pressure has zero spatial gradient
everywhere. -/
theorem ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_zero_iff_spatialPressureGradient_zero
    {ν : ℝ} {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν (0 : NSInitialVelocity) (0 : NSVelocityField) p ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hu, _hp, hmom, _hdiv, _hinit, _henergy⟩ t x
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simpa [timeVelocityDerivative_zero, spatialConvection_zero, hlap] using
      hmom t x
  · intro hgrad
    refine ⟨?_, hp, ?_, ?_, ?_, ?_⟩
    · simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
    · intro t x
      have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
        simpa [constantVelocityField] using
          spatialLaplacian_constantVelocityField (0 : NSSpace) t x
      simp [timeVelocityDerivative_zero, spatialConvection_zero, hlap, hgrad t x]
    · intro t x
      simpa using (spatialDivergence_zero t x)
    · intro x
      rfl
    · refine ⟨0, le_rfl, ?_⟩
      intro t
      constructor
      · have hk :
            kineticEnergyDensity (0 : NSVelocityField) t =
              (fun _ : NSSpace => (0 : ℝ)) := by
          funext x
          simp [kineticEnergyDensity]
        rw [hk]
        exact
          MeasureTheory.integrable_zero NSSpace ℝ
            (MeasureTheory.volume : MeasureTheory.Measure NSSpace)
      · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
          simp [kineticEnergyAt, kineticEnergyDensity]
        simp [hE0]

/-- A single nonzero spatial-pressure-gradient point rules out the zero
velocity / fixed-pressure exact whole-space output surface. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_zero_of_exists_spatialPressureGradient_ne_zero
    {ν : ℝ} {p : NSPressureField}
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν (0 : NSInitialVelocity) (0 : NSVelocityField) p := by
  intro hGlobal
  rcases hbad with ⟨t, x, hne⟩
  have hp : smoothSpaceTimePressure p := hGlobal.2.1
  exact hne
    ((ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_zero_iff_spatialPressureGradient_zero
      (ν := ν) (p := p) hp).1 hGlobal t x)

/-- On the cancelled equal-amplitude anti-profile branch, exact whole-space
outputs with a fixed arbitrary smooth pressure exist exactly when that pressure
has zero spatial gradient everywhere. -/
theorem
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero
    {ν : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        p ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  rw [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f,
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f]
  exact
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_zero_iff_spatialPressureGradient_zero
      (ν := ν) (p := p) hp

/-- Therefore any nonzero spatial-pressure-gradient point rules out the exact
whole-space output surface on the cancelled equal-amplitude anti-profile
branch, independently of the pressure family. -/
theorem
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero
    {ν : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        p := by
  intro hGlobal
  rcases hbad with ⟨t, x, hne⟩
  have hp : smoothSpaceTimePressure p := hGlobal.2.1
  exact hne
    ((ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero
      (ν := ν) a f (p := p) hp).1 hGlobal t x)

/-- The affine-plus-localized Schwartz pressure subclass has no extra whole-space
repair freedom on the cancelled equal-amplitude anti-profile branch. Exact
global outputs exist exactly when the affine coefficient vanishes at every time,
and any active localized amplitude forces the fixed Schwartz pressure gradient
to vanish everywhere. -/
theorem
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
    {ν : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        (affineAddScalarSchwartzPressure c π ρ q) ↔
      (∀ t, c t = 0) ∧
        ((∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  have hp :
      smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q
  constructor
  · rintro ⟨_hu, _hp, hmom, _hdiv, _hinit, _henergy⟩
    exact
      (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
        a ν c π ρ f q).1 hmom
  · intro hcollapse
    have hmom :
        ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
      exact
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
          a ν c π ρ f q).2 hcollapse
    have hgrad :
        ∀ t x,
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x = 0 := by
      exact
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          a ν f (affineAddScalarSchwartzPressure c π ρ q)).1 hmom
    exact
      (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero
        (ν := ν)
        a
        f
        (p := affineAddScalarSchwartzPressure c π ρ q)
        hp).2 hgrad

/-- Negative form of the same affine-plus-localized whole-space classification:
the cancelled equal-amplitude anti-profile branch cannot be an exact whole-space
output if the affine coefficient is nonzero somewhere, or if an active
localized amplitude is paired with a nonzero fixed Schwartz pressure gradient. -/
theorem
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_or_active_schwartzPressureGradient_ne_zero
    {ν : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, c t ≠ 0) ∨
        ((∃ t, ρ t ≠ 0) ∧
          ∃ s, ∃ x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        (affineAddScalarSchwartzPressure c π ρ q) := by
  intro hGlobal
  have hcollapse :=
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
      (ν := ν) a c π ρ f q hc hπ hρ).1 hGlobal
  rcases hcollapse with ⟨hcZero, hgradZero⟩
  cases hbad with
  | inl hcoeff =>
      rcases hcoeff with ⟨t, hne⟩
      exact hne (hcZero t)
  | inr hactive =>
      rcases hactive with ⟨hρactive, s, x, hgradne⟩
      exact hgradne (hgradZero hρactive s x)

end NavierStokes
end FluidDynamics
end Mettapedia
