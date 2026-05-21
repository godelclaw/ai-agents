import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLocalExistencePrerequisites
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Witness-Construction Global-Output Obstruction

This file lifts exact finite-time witness impossibility results to the exact
whole-space output surface for a fixed velocity/pressure pair. If a pair cannot
occur even on one finite slab, then it cannot occur as a global explicit
Navier--Stokes output either.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Exact whole-space output surface with both the velocity and pressure fixed
in advance. This is the direct global analogue of the exact finite-time witness
surface. -/
def ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
    (ν : ℝ) (u₀ : NSInitialVelocity) (u : NSVelocityField) (p : NSPressureField) : Prop :=
  smoothSpaceTimeVelocity u ∧
    smoothSpaceTimePressure p ∧
    (∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) ∧
    (∀ t x, spatialDivergence u t x = 0) ∧
    MatchesInitialVelocity u₀ u ∧
    boundedKineticEnergy u

/-- The prescribed-velocity global-output surface is exactly the existential
closure of the prescribed velocity/pressure surface. -/
theorem ExplicitConcreteNavierStokesGlobalOutputWithVelocity_iff_exists_pressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u ↔
      ∃ p : NSPressureField,
        ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p := by
  rfl

/-- Any exact whole-space output for a fixed velocity/pressure pair restricts
to an exact finite-time witness on every slab. -/
theorem ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.implies_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧ W.pressure = p := by
  rcases h with ⟨hu, hp, hmom, hdiv, hinit, hbd⟩
  refine ⟨{
    velocity := u
    pressure := p
    smooth_velocity := hu
    smooth_pressure := hp
    momentum_equation_on := by
      intro t x _ht0 _htT
      exact hmom t x
    incompressible_on := by
      intro t x _ht0 _htT
      exact hdiv t x
    initial_condition := hinit
    bounded_energy_on := boundedKineticEnergy_implies_boundedKineticEnergyUpTo hbd
  }, rfl, rfl⟩

/-- Contrapositively, a fixed velocity/pressure pair that cannot occur as a
finite-time witness on some slab cannot occur as an exact whole-space output
either. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p := by
  intro hGlobal
  exact hW
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.implies_finiteTimeWitness
      (T := T) hGlobal)

/-- A finite-energy stationary seed has global bounded kinetic energy, not only
slabwise bounded energy. -/
theorem boundedKineticEnergy_timeIndependentVelocity
    {u₀ : NSInitialVelocity}
    (hE : finiteInitialKineticEnergy u₀) :
    boundedKineticEnergy (timeIndependentVelocity u₀) := by
  refine ⟨kineticEnergyAt (timeIndependentVelocity u₀) 0,
    kineticEnergyAt_nonneg (timeIndependentVelocity u₀) 0, ?_⟩
  intro t
  constructor
  · simpa [kineticEnergyDensity_timeIndependentVelocity, finiteInitialKineticEnergy] using hE
  · rw [kineticEnergyAt_timeIndependentVelocity,
      kineticEnergyAt_timeIndependentVelocity]

/-- A time-independent seed gives an exact whole-space output with a fixed
pressure field exactly when that seed and pressure satisfy the stationary
momentum balance everywhere.  This is the global analogue of the slabwise
finite-time witness classification. -/
theorem timeIndependentVelocity_globalOutputWithVelocityPressure_iff_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity} (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀)
    (hp : smoothSpaceTimePressure p) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν u₀ (timeIndependentVelocity u₀) p ↔
      (∀ t x,
        spatialConvection (timeIndependentVelocity u₀) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  constructor
  · rintro ⟨_hu, _hp, hmom, _hinc, _hinit, _hbd⟩ t x
    have htime :
        timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
      exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
    simpa [htime] using hmom t x
  · intro hstationary
    refine ⟨smoothSpaceTimeVelocity_timeIndependentVelocity hsmooth, hp, ?_, ?_, ?_, ?_⟩
    · intro t x
      have htime :
          timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
        exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
      simpa [htime] using hstationary t x
    · intro t x
      calc
        spatialDivergence (timeIndependentVelocity u₀) t x =
            initialSpatialDivergence u₀ x := by
              exact spatialDivergence_timeIndependentVelocity u₀ t x
        _ = 0 := hdiv x
    · exact MatchesInitialVelocity_timeIndependentVelocity u₀
    · exact boundedKineticEnergy_timeIndependentVelocity henergy

/-- The boxed steady seed attached to a finite-energy boxed datum also has
global bounded kinetic energy. -/
theorem boundedKineticEnergy_boxedPartialPeriodizationSteadySeed
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    boundedKineticEnergy (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) := by
  simpa [boxedPartialPeriodizationSteadySeedVelocity,
    boxedPartialPeriodizationNavierStokesProblemData,
    FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData] using
    boundedKineticEnergy_timeIndependentVelocity
      (u₀ := (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).initialVelocity)
      (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).finite_initial_energy

/-- Any fixed smooth pressure gauge with zero spatial gradient leaves the
boxed steady seed on the exact whole-space output surface exactly at the
zero-pressure stationary momentum boundary. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_globalOutputWithVelocityPressure_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p ↔
      (∀ t x,
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  constructor
  · rintro ⟨_hu, _hp, hmom, _hdiv, _hinit, _hbd⟩ t x
    rcases boxedPartialPeriodizationSteadySeed_basic hν N L u₀ with
      ⟨_hsmooth, _hinitBasic, _hdivBasic, htime, _henergyDensity⟩
    simpa [htime t x, hp_zero t x] using hmom t x
  · intro hstationary
    rcases boxedPartialPeriodizationSteadySeed_basic hν N L u₀ with
      ⟨hsmooth, hinit, hdiv, htime, _henergyDensity⟩
    refine ⟨hsmooth, hp, ?_, hdiv, hinit,
      boundedKineticEnergy_boxedPartialPeriodizationSteadySeed hν N L u₀⟩
    intro t x
    simpa [htime t x, hp_zero t x] using hstationary t x

/-- The exact whole-space output layer adds no escape hatch to the
stationary-momentum audit for time-independent seeds. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_timeIndependentVelocity_of_stationaryMomentum_failure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν u₀ (timeIndependentVelocity u₀) p := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
      (not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
        (ν := ν)
        (u₀ := u₀)
        (T := T)
        (p := p)
        (t := t)
        (x := x)
        ht0
        htT
        hfail)

/-- Boxed-periodization instance of the exact whole-space obstruction:
stationary momentum failure at one slab point rules out the exact seed/pressure
pair as a global explicit output. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
      (not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀
        (p := p)
        ht0
        htT
        hfail)

/-- The same exact whole-space obstruction holds uniformly across all smooth
zero-spatial-gradient pressure gauges. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p := by
  have hfail' :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
    simpa [hp_zero t x] using hfail
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail'

/-- A single failed zero-pressure stationary residual rules out the whole
smooth zero-spatial-gradient pressure repair class on the exact whole-space
output surface for the boxed steady seed. -/
theorem
    not_exists_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
            ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p := by
  intro hGlobal
  rcases hGlobal with ⟨p, _hp, hp_zero, hOut⟩
  exact
    (not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
      hν N L u₀ (p := p) hp_zero ht0 htT hfail) hOut

/-- In particular, a smooth time-only pressure gauge cannot rescue a boxed
steady seed on the exact whole-space output surface either. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
      hν N L u₀
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      ht0
      htT
      hfail

/-- Candidate-level exact global-output obstruction for the boxed-periodization
steady seed with an arbitrary smooth zero-spatial-gradient pressure gauge: the
seed already carries every whole-space output field except the momentum
equation, but a failed zero-pressure stationary residual still prevents that
fixed velocity/pressure pair from being a global explicit output. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_exhibits_nonMomentumGlobalFields_without_exactGlobalOutput
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        p := by
  rcases boxedPartialPeriodizationSteadySeed_basic hν N L u₀ with
    ⟨hsmooth, hinit, hdiv, _htime, _henergyDensity⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hsmooth, hp, hdiv, hinit,
      boundedKineticEnergy_boxedPartialPeriodizationSteadySeed hν N L u₀⟩
  · exact
      not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_of_stationaryMomentum_failure
        hν N L u₀ (p := p) hp_zero ht0 htT hfail

/-- Candidate-level exact global-output obstruction for the boxed-periodization
steady seed with a smooth time-only pressure gauge: the seed already carries
all whole-space output fields except the momentum equation, but a stationary
residual failure still prevents that exact velocity/pressure pair from being a
global explicit output. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumGlobalFields_without_exactGlobalOutput
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun t : NSTime => fun _ : NSSpace => π t) := by
  rcases boxedPartialPeriodizationSteadySeed_basic hν N L u₀ with
    ⟨hsmooth, hinit, hdiv, _htime, _henergyDensity⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hsmooth, smoothSpaceTimePressure_timeOnly hπ, hdiv, hinit,
      boundedKineticEnergy_boxedPartialPeriodizationSteadySeed hν N L u₀⟩
  · exact
      not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail

end NavierStokes
end FluidDynamics
end Mettapedia
