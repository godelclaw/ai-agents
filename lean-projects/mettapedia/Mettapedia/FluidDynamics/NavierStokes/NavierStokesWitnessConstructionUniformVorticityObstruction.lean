import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Witness-Construction Uniform-Vorticity Obstruction

This file lifts exact finite-time witness impossibility results to the
uniform-vorticity-packaged data surface. Adding a slab vorticity bound cannot
rescue a velocity/pressure pair that already fails the exact finite-time witness
obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- If an exact velocity/pressure pair cannot occur as a finite-time witness,
then it also cannot occur after adding a uniform slab vorticity bound. -/
theorem not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  intro hData
  apply hW
  rcases hData with ⟨W, hWvel, hWpress, _B, _hω⟩
  exact ⟨W, hWvel, hWpress⟩

/-- The uniform-vorticity layer adds no escape hatch to the stationary-momentum
audit for time-independent seeds. -/
theorem not_exists_timeIndependentVelocity_uniformVorticityData_of_stationaryMomentum_failure
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
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness
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

/-- For a time-independent Schwartz seed, the uniform-vorticity-packaged
witness surface is exactly the same stationary-momentum surface as the
underlying finite-time witness audit.  The uniform vorticity bound is supplied
internally by the first Schwartz seminorm of the seed. -/
theorem timeIndependentVelocity_schwartz_uniformVorticityData_iff_stationaryMomentum
    {ν T : ℝ} (u₀ : NSSchwartzInitialVelocity) (p : NSPressureField)
    (hdiv : ∀ x, initialSpatialDivergence (u₀ : NSInitialVelocity) x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (u₀ : NSInitialVelocity) T,
        W.velocity = timeIndependentVelocity (u₀ : NSInitialVelocity) ∧
          W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity (u₀ : NSInitialVelocity)) t x := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _B, _hω⟩
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
    refine
      ⟨W, hWvel, hWpress, schwartzInitialVelocityVorticityBound u₀, ?_⟩
    simpa [hWvel] using
      (uniformVorticityBoundUpTo_timeIndependentVelocity u₀ T)

/-- Boxed-periodization uniform-vorticity-data classification for the steady
seed.  The slab vorticity bound is not an additional repair parameter for this
exact boxed seed: it is already supplied by the finite Schwartz periodization
profile, so the remaining condition is exactly the stationary momentum balance
on the slab. -/
theorem boxedPartialPeriodizationSteadySeed_uniformVorticityData_iff_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _B, _hω⟩
    exact
      boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
        hν N L u₀ ⟨W, hWvel, hWpress⟩
  · intro hstationary
    rcases
        (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
          hν N L u₀ T p hp).2 hstationary with
      ⟨W, hWvel, hWpress⟩
    refine
      ⟨W, hWvel, hWpress,
        schwartzInitialVelocityVorticityBound
          (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1, ?_⟩
    simpa [hWvel, boxedPartialPeriodizationSteadySeedVelocity,
      boxedPartialPeriodizationNavierStokesProblemData,
      boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData,
      NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData]
      using
        (uniformVorticityBoundUpTo_timeIndependentVelocity
          (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1 T)

/-- Boxed-periodization instance of the uniform-vorticity-layer steady-seed
obstruction: stationary momentum failure at one slab point rules out the exact
seed/pressure pair even after adding a slab vorticity bound. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_uniformVorticityData_of_stationaryMomentum_failure
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
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness
      (not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀
        (p := p)
        ht0
        htT
        hfail)

/-- The same uniform-vorticity-layer obstruction holds uniformly across all
smooth zero-spatial-gradient pressure gauges. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_uniformVorticityData_of_stationaryMomentum_failure
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
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  have hfail' :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
    simpa [hp_zero t x] using hfail
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_uniformVorticityData_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail'

/-- In particular, a smooth time-only pressure gauge cannot rescue a boxed
steady seed at the uniform-vorticity-data layer either. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_uniformVorticityData_of_stationaryMomentum_failure
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
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_uniformVorticityData_of_stationaryMomentum_failure
      hν N L u₀
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      ht0
      htT
      hfail

/-- Candidate-level uniform-vorticity obstruction for the boxed-periodization
steady seed with a smooth time-only pressure gauge: the seed already carries
the non-momentum witness fields, but a stationary residual failure still
prevents any uniform-vorticity-packaged use of that exact velocity/pressure
pair. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_uniformVorticityData
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
            ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  refine ⟨?_, ?_⟩
  · exact
      (boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
        hν N L u₀ T π hπ ht0 htT hfail).1
  · exact
      not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_uniformVorticityData_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail

end NavierStokes
end FluidDynamics
end Mettapedia
