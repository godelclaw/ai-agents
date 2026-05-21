import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Witness-Construction BKM Obstruction

This file lifts exact finite-time witness impossibility results to the BKM data
surface.  Adding a vorticity envelope and an integral budget cannot rescue a
velocity/pressure pair that already fails the exact finite-time witness
obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- If an exact velocity/pressure pair cannot occur as a finite-time witness,
then it also cannot occur after adding BKM envelope data. -/
theorem not_exists_BKMData_of_not_exists_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  intro hData
  apply hW
  rcases hData with ⟨W, hWvel, hWpress, _Ω, _B, _hEnv, _hInt⟩
  exact ⟨W, hWvel, hWpress⟩

/-- The BKM envelope layer adds no escape hatch to the stationary-momentum
audit for time-independent seeds. -/
theorem not_exists_timeIndependentVelocity_BKMData_of_stationaryMomentum_failure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_BKMData_of_not_exists_finiteTimeWitness
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

/-- For a time-independent Schwartz seed, the BKM-packaged witness surface is
exactly the same stationary-momentum surface as the underlying finite-time
witness audit.  The extra BKM envelope data are supplied internally by the
Schwartz vorticity seminorm bound, so they add no independent analytic
obligation for this exact seed. -/
theorem timeIndependentVelocity_schwartz_BKMData_iff_stationaryMomentum
    {ν T : ℝ} (u₀ : NSSchwartzInitialVelocity) (p : NSPressureField)
    (hdiv : ∀ x, initialSpatialDivergence (u₀ : NSInitialVelocity) x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (u₀ : NSInitialVelocity) T,
        W.velocity = timeIndependentVelocity (u₀ : NSInitialVelocity) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _Ω, _B, _hEnv, _hInt⟩
    exact
      timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
        (ν := ν)
        (u₀ := (u₀ : NSInitialVelocity))
        (T := T)
        (p := p)
        ⟨W, hWvel, hWpress⟩
  · intro hstationary
    rcases
        (timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
          (ν := ν)
          (u₀ := (u₀ : NSInitialVelocity))
          (T := T)
          p
          (smoothInitialVelocityData_of_schwartzInitialVelocity u₀)
          hdiv
          (finiteInitialKineticEnergy_of_schwartzInitialVelocity u₀)
          hp).2 hstationary with
      ⟨W, hWvel, hWpress⟩
    rcases timeIndependentVelocity_exhibits_BKMEnvelope u₀ T with
      ⟨Ω, B, hEnv, hInt⟩
    refine ⟨W, hWvel, hWpress, Ω, B, ?_, hInt⟩
    simpa [hWvel] using hEnv

/-- Boxed-periodization BKM-data classification for the steady seed.  The BKM
envelope is not an additional repair parameter for this exact boxed seed: it is
already supplied by the finite Schwartz periodization profile, so the remaining
condition is exactly the stationary momentum balance on the slab. -/
theorem boxedPartialPeriodizationSteadySeed_BKMData_iff_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _Ω, _B, _hEnv, _hInt⟩
    exact
      boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
        hν N L u₀ ⟨W, hWvel, hWpress⟩
  · intro hstationary
    rcases
        (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
          hν N L u₀ T p hp).2 hstationary with
      ⟨W, hWvel, hWpress⟩
    rcases
        timeIndependentVelocity_exhibits_BKMEnvelope
          (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1 T with
      ⟨Ω, B, hEnv, hInt⟩
    refine ⟨W, hWvel, hWpress, Ω, B, ?_, hInt⟩
    simpa [hWvel, boxedPartialPeriodizationSteadySeedVelocity,
      boxedPartialPeriodizationNavierStokesProblemData,
      boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData,
      NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData]
      using hEnv

/-- Any smooth pressure gauge with zero spatial gradient leaves the boxed
steady-seed BKM-data criterion unchanged: the packaged finite-time data exist
exactly when the zero-pressure stationary momentum balance already holds on the
slab. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  constructor
  · intro hData t x ht0 htT
    have hstat :=
      (boxedPartialPeriodizationSteadySeed_BKMData_iff_stationaryMomentum
        hν N L u₀ T p hp).1 hData t x ht0 htT
    simpa [hp_zero t x] using hstat
  · intro hstat
    refine
      (boxedPartialPeriodizationSteadySeed_BKMData_iff_stationaryMomentum
        hν N L u₀ T p hp).2 ?_
    intro t x ht0 htT
    simpa [hp_zero t x] using hstat t x ht0 htT

/-- In particular, a smooth time-only pressure gauge does not enlarge the
boxed steady-seed BKM-data surface: the exact criterion is still the
zero-pressure stationary momentum balance on the slab. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_BKMData_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- On the boxed steady-seed BKM-data surface, every smooth
zero-spatial-gradient pressure gauge is propositionally equivalent to the
literal zero-pressure representative. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) ↔
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T p hp hp_zero).trans
      ((boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
        hν N L u₀ T
        (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ))
        (by simpa using smoothSpaceTimePressure_const (0 : ℝ))
        (by
          intro t x
          simpa using spatialPressureGradient_zero t x)).symm)

/-- Allowing an arbitrary smooth zero-spatial-gradient pressure gauge does not
enlarge the boxed steady-seed BKM-data surface: such packaged data exist for
some harmless gauge exactly when the zero-pressure stationary momentum balance
already holds on the slab. -/
theorem
    exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    (∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ∃ W :
            ExplicitFiniteTimeRegularityWitness ν
              (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
            W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
              W.pressure = p ∧
              ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
                vorticityEnvelopeOn W.velocity T Ω ∧
                  integrableVorticityEnvelopeOn Ω T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  constructor
  · rintro ⟨p, hp, hp_zero, hData⟩
    exact
      (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
        hν N L u₀ T p hp hp_zero).1 hData
  · intro hstat
    refine ⟨fun _ : NSTime => fun _ : NSSpace => (0 : ℝ), ?_, ?_, ?_⟩
    · simpa using smoothSpaceTimePressure_const (0 : ℝ)
    · intro t x
      simpa using spatialPressureGradient_zero t x
    · exact
        (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_iff_stationaryMomentum_zeroPressure
          hν N L u₀ T
          (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ))
          (by simpa using smoothSpaceTimePressure_const (0 : ℝ))
          (by
            intro t x
            simpa using spatialPressureGradient_zero t x)).2 hstat

/-- Boxed-periodization instance of the BKM-layer steady-seed obstruction:
stationary momentum failure at one slab point rules out the exact seed/pressure
pair even after adding a BKM envelope. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_BKMData_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_BKMData_of_not_exists_finiteTimeWitness
      (not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀
        (p := p)
        ht0
        htT
        hfail)

/-- The same BKM-layer obstruction holds uniformly across all smooth
zero-spatial-gradient pressure gauges. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  have hfail' :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
    simpa [hp_zero t x] using hfail
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_BKMData_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail'

/-- In particular, a smooth time-only pressure gauge cannot rescue a boxed
steady seed at the BKM-data layer either. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_BKMData_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_BKMData_of_stationaryMomentum_failure
      hν N L u₀
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      ht0
      htT
      hfail

/-- Candidate-level BKM obstruction for the boxed-periodization steady seed
with a smooth time-only pressure gauge: the seed already carries the
non-momentum witness fields, but a stationary residual failure still prevents
any BKM-packaged use of that exact velocity/pressure pair. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_BKMData
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
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
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T) ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
          W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
            ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T B := by
  refine ⟨?_, ?_⟩
  · exact
      (boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
        hν N L u₀ T π hπ ht0 htT hfail).1
  · exact
      not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_BKMData_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail

end NavierStokes
end FluidDynamics
end Mettapedia
