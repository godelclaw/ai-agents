import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLocalExistencePrerequisites

/-!
# Concrete Navier-Stokes Witness Construction

This file keeps the witness-construction surface honest.  It records the
direct zero-data global witness, and it classifies the boxed steady seed route:
the seed becomes a finite-time witness exactly when the stationary momentum
balance is supplied on the slab.  Thus the boxed seed is not a local existence
theorem for general data; the missing step is an evolved solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff

section ConcreteWitnessConstruction

/-- The zero velocity and zero pressure fields form an actual global witness
for the fully concrete Navier-Stokes record at zero initial data. -/
def zeroNavierStokesGlobalRegularityWitness
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityWitness
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } where
  velocity := 0
  pressure := 0
  smooth_velocity := by
    simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
  smooth_pressure := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  momentum_equation := by
    intro t x
    exact momentumEquation_zeroVelocityField_zeroPressure ν t x
  incompressible := by
    intro t x
    simpa using (spatialDivergence_zero t x)
  initial_condition := by
    intro x
    rfl
  bounded_energy := by
    refine ⟨0, le_rfl, ?_⟩
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

/-- The direct zero global witness inhabits the structured fully concrete
global-regularity clause. -/
theorem zeroNavierStokesGlobalRegularityWitness_nonempty
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact ⟨zeroNavierStokesGlobalRegularityWitness hν⟩

/-- For a fixed pressure field, the boxed steady seed gives a finite-time
witness with that exact velocity and pressure if and only if the stationary
momentum balance holds on the slab.  This is a classification theorem, not a
local-existence theorem: for general boxed data the balance is precisely the
hard missing equation. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    have htime :
        timeVelocityDerivative (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          0 := by
      exact (boxedPartialPeriodizationSteadySeed_basic hν N L u₀).2.2.2.1 t x
    simpa [htime] using hmom
  · intro hstationary
    rcases boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields hν N L u₀ T with
      ⟨hsmooth, _hzeroPressure, hdiv, hinit, henergy⟩
    let W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T :=
      { velocity := boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν
        pressure := p
        smooth_velocity := hsmooth
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have htime :
              timeVelocityDerivative
                  (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
                0 := by
            exact (boxedPartialPeriodizationSteadySeed_basic hν N L u₀).2.2.2.1 t x
          simpa [htime] using hstationary t x ht0 htT
        incompressible_on := by
          intro t x ht0 htT
          exact hdiv t x
        initial_condition := hinit
        bounded_energy_on := henergy }
    exact ⟨W, rfl, rfl⟩

end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
