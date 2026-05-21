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

/-- For a finite-energy smooth divergence-free initial datum, the
time-independent seed supplies every finite-time witness field except the
momentum equation and the pressure.  This isolates the exact analytic work
needed before a compatibility seed can be upgraded to a local solution. -/
theorem timeIndependentVelocity_nonMomentumFiniteTimeFields
    {u₀ : NSInitialVelocity} (T : ℝ)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀) :
    smoothSpaceTimeVelocity (timeIndependentVelocity u₀) ∧
      (∀ t x, spatialDivergence (timeIndependentVelocity u₀) t x = 0) ∧
      (∀ t x, timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0) ∧
      MatchesInitialVelocity u₀ (timeIndependentVelocity u₀) ∧
      boundedKineticEnergyUpTo (timeIndependentVelocity u₀) T := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_timeIndependentVelocity hsmooth
  · intro t x
    calc
      spatialDivergence (timeIndependentVelocity u₀) t x =
          initialSpatialDivergence u₀ x := by
            exact spatialDivergence_timeIndependentVelocity u₀ t x
      _ = 0 := hdiv x
  · exact timeVelocityDerivative_timeIndependentVelocity u₀
  · exact MatchesInitialVelocity_timeIndependentVelocity u₀
  · exact boundedKineticEnergyUpTo_timeIndependentVelocity henergy

/-- A time-independent seed gives a finite-time Navier-Stokes witness with a
fixed pressure field exactly when that seed and pressure satisfy the stationary
momentum balance throughout the slab.  This is the general version of the boxed
steady-seed obstruction: compatibility data are not local existence data unless
the momentum equation is also supplied. -/
theorem timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (T : ℝ) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity u₀) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    have htime :
        timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
      exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
    simpa [htime] using hmom
  · intro hstationary
    rcases timeIndependentVelocity_nonMomentumFiniteTimeFields
        (u₀ := u₀) T hsmooth hdiv henergy with
      ⟨hvel, hinc, htime, hinit, hbd⟩
    let W : ExplicitFiniteTimeRegularityWitness ν u₀ T :=
      { velocity := timeIndependentVelocity u₀
        pressure := p
        smooth_velocity := hvel
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          simpa [htime t x] using hstationary t x ht0 htT
        incompressible_on := by
          intro t x _ht0 _htT
          exact hinc t x
        initial_condition := hinit
        bounded_energy_on := hbd }
    exact ⟨W, rfl, rfl⟩

/-- On a nonnegative slab, a time-independent seed with fixed pressure gives a
finite-time witness exactly when the datum has finite kinetic energy and the
stationary momentum balance holds.  This folds the previously external
bounded-energy side condition into the witness-existence statement itself. -/
theorem timeIndependentVelocity_finiteTimeWitness_iff_finiteInitialKineticEnergy_and_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      finiteInitialKineticEnergy u₀ ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          spatialConvection (timeIndependentVelocity u₀) t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · rcases hW with ⟨W, hWvel, hWpress⟩
      exact W.finiteInitialKineticEnergy hT
    · rcases hW with ⟨W, hWvel, hWpress⟩
      intro t x ht0 htT
      have hmom := W.momentum_equation_on t x ht0 htT
      rw [hWvel, hWpress] at hmom
      have htime :
          timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
        exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
      simpa [htime] using hmom
  · rintro ⟨henergy, hstationary⟩
    exact
      (timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
        T p hsmooth hdiv henergy hp).2 hstationary

/-- Any finite-time witness whose velocity is a time-independent seed and
whose pressure is the fixed pressure field forces the stationary momentum
balance on the whole slab.  This is the forward audit direction separated from
the construction-side hypotheses of the iff theorem. -/
theorem timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x := by
  rcases hW with ⟨W, hWvel, hWpress⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  rw [hWvel, hWpress] at hmom
  have htime :
      timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
    exact timeVelocityDerivative_timeIndependentVelocity u₀ t x
  simpa [htime] using hmom

/-- Time-zero form of the exact time-independent seed audit.  On a nonnegative
slab, exact finite-time use of a time-independent seed must already solve the
stationary momentum balance at the initial slice. -/
theorem timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum_zero_time
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ x,
      spatialConvection (timeIndependentVelocity u₀) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) 0 x := by
  intro x
  exact
    timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      hW 0 x le_rfl hT

/-- A single failed stationary momentum equation at one point of the slab rules
out any finite-time witness whose velocity is the corresponding
time-independent seed and whose pressure is the fixed pressure field.  Unlike
the iff theorem above, this negative audit does not need smoothness or
finite-energy hypotheses: those would be carried by the putative witness
itself. -/
theorem not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p := by
  intro hW
  exact hfail
    (timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      hW t x ht0 htT)

/-- Any finite-time witness with zero velocity and fixed pressure forces that
pressure to have zero spatial gradient throughout the slab.  This separates
the harmless time-only pressure gauge from pressure fields that would introduce
a nonzero force even when the velocity is zero. -/
theorem zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rcases hW with ⟨W, hWvel, hWpress⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  rw [hWvel, hWpress] at hmom
  have hlap :
      spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [timeVelocityDerivative_zero, spatialConvection_zero, hlap] using hmom

/-- Zero velocity with a fixed smooth pressure field gives a finite-time
Navier-Stokes witness exactly when the pressure has zero spatial gradient on
the slab.  This is the pressure-gauge baseline behind the zero-data route:
time-only pressure gauges are harmless, while spatial pressure gradients are
real forcing terms. -/
theorem zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  constructor
  · exact zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
  · intro hgrad
    let W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T :=
      { velocity := 0
        pressure := p
        smooth_velocity := by
          simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
            (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have hlap :
              spatialLaplacian (0 : NSVelocityField) t x = 0 := by
            simpa [constantVelocityField] using
              spatialLaplacian_constantVelocityField (0 : NSSpace) t x
          have hpx : spatialPressureGradient p t x = 0 := hgrad t x ht0 htT
          simp [timeVelocityDerivative_zero, spatialConvection_zero, hlap, hpx]
        incompressible_on := by
          intro t x _ht0 _htT
          simpa using (spatialDivergence_zero t x)
        initial_condition := by
          intro x
          rfl
        bounded_energy_on := by
          refine ⟨0, le_rfl, ?_⟩
          intro t _ht0 _htT
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
            simp [hE0] }
    exact ⟨W, rfl, rfl⟩

/-- Positive pressure-gauge instance of the zero-velocity classification: any
smooth time-only pressure gives a finite-time zero-velocity witness, because it
has zero spatial gradient on every slice. -/
theorem zeroVelocity_timeOnlyPressure_finiteTimeWitness
    {ν : ℝ} {T : ℝ} (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    (zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
      (ν := ν)
      (T := T)
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)).mpr
      (by
        intro t x _ht0 _htT
        exact spatialPressureGradient_timeOnly π t x)

/-- Constant velocity with a fixed smooth pressure field gives a finite-time
witness on a nonnegative slab exactly when the field is actually zero and the
pressure has zero spatial gradient on that slab.  This closes the tempting
constant-field ansatz completely at the exact witness surface. -/
theorem constantVelocityField_finiteTimeWitness_iff_zero_and_spatialPressureGradient_zero
    {ν : ℝ} {T : ℝ} (hT : 0 ≤ T) {c : NSSpace} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T,
        W.velocity = constantVelocityField c ∧ W.pressure = p) ↔
      c = 0 ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  constructor
  · intro hW
    rcases hW with ⟨W, hWvel, hWpress⟩
    have hbd : boundedKineticEnergyUpTo (constantVelocityField c) T := by
      simpa [hWvel] using W.bounded_energy_on
    have hc0 : c = 0 := by
      exact
        (boundedKineticEnergyUpTo_constantVelocityField_iff
          (T := T) (c := c) hT).1 hbd
    refine ⟨hc0, ?_⟩
    subst hc0
    have hW0 :
        ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = (0 : NSVelocityField) ∧ W.pressure = p := by
      simpa [constantInitialVelocity, constantVelocityField] using
        (show ∃ W : ExplicitFiniteTimeRegularityWitness ν
            (constantInitialVelocity (0 : NSSpace)) T,
            W.velocity = constantVelocityField (0 : NSSpace) ∧ W.pressure = p from
            ⟨W, hWvel, hWpress⟩)
    exact zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero hW0
  · rintro ⟨hc0, hgrad⟩
    subst hc0
    have hW0 :
        ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = (0 : NSVelocityField) ∧ W.pressure = p := by
      exact
        (zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) p hp).2 hgrad
    simpa [constantInitialVelocity, constantVelocityField] using hW0

/-- On a nonnegative slab, the entire finite-time witness type for constant
initial data is inhabited exactly in the zero-data case.  This closes not only
the literal constant-field ansatz, but every possible witness route from
nonzero constant initial data. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {c : NSSpace} :
    Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) ↔
      c = 0 := by
  constructor
  · intro hW
    by_contra hc
    exact
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT) hW
  · intro hc
    subst hc
    rcases zeroVelocity_timeOnlyPressure_finiteTimeWitness
        (ν := ν) (T := T) (fun _ : NSTime => (0 : ℝ))
        (by simpa using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))) with
      ⟨W, _hWvel, _hWpress⟩
    exact ⟨W⟩

/-- A single nonzero spatial pressure gradient rules out any finite-time
zero-velocity witness with that fixed pressure field. -/
theorem not_exists_zeroVelocity_finiteTimeWitness_of_spatialPressureGradient_failure
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail : spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p := by
  intro hW
  exact hfail
    (zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero
      hW t x ht0 htT)

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
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  have henergy : finiteInitialKineticEnergy P.initialVelocity := by
    simpa [P, boxedPartialPeriodizationNavierStokesProblemData,
      FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData] using
      (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).finite_initial_energy
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      P.smooth_initial
      P.divergence_free_initial
      henergy
      hp)

/-- Any smooth pressure gauge with zero spatial gradient leaves the boxed
steady-seed witness criterion unchanged: the exact finite-time witness
condition is still the zero-pressure stationary momentum balance on the slab. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  constructor
  · intro hW t x ht0 htT
    have hstat :=
      (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
        hν N L u₀ T p hp).1 hW t x ht0 htT
    simpa [hp_zero t x] using hstat
  · intro hstat
    refine
      (boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
        hν N L u₀ T p hp).2 ?_
    intro t x ht0 htT
    simpa [hp_zero t x] using hstat t x ht0 htT

/-- A smooth time-only pressure gauge does not change the boxed steady-seed
stationary audit: because its spatial gradient vanishes identically, the exact
finite-time witness condition is still the zero-pressure stationary momentum
balance on the slab. -/
theorem boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t)) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Boxed-periodization instance of the forward audit: if the steady boxed seed
is the exact finite-time witness velocity with fixed pressure, then the
stationary momentum balance holds on the whole slab. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      (by simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using hW))

/-- Time-zero boxed-periodization audit: exact finite-time use of the steady
boxed seed on a nonnegative slab must solve the stationary momentum balance at
the initial slice. -/
theorem boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum_zero_time
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ x,
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x := by
  intro x
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
      hν N L u₀ hW 0 x le_rfl hT

/-- Boxed-periodization instance of the pointwise stationary-residual audit:
if the steady boxed seed and fixed pressure fail the stationary momentum
equation anywhere on the slab, that exact seed cannot be the finite-time
witness. -/
theorem not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
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
          W.pressure = p := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
    (not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
      (ν := ν)
      (u₀ := P.initialVelocity)
      (T := T)
      (p := p)
      (t := t)
      (x := x)
      ht0
      htT
      (by simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using hfail))

/-- A smooth zero-spatial-gradient pressure gauge cannot rescue a boxed steady
seed whose zero-pressure stationary residual already fails somewhere on the
slab. -/
theorem
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p := by
  have hfail' :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
    simpa [hp_zero t x] using hfail
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT
      (p := p)
      hfail'

/-- In particular, a smooth time-only pressure gauge cannot rescue a boxed
steady seed whose zero-pressure stationary residual already fails somewhere on
the slab. -/
theorem
    not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
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
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      ht0 htT hfail

/-- Candidate-level obstruction for the boxed-periodization steady seed with a
smooth time-only pressure gauge: all non-momentum finite-time witness fields are
available, but if the zero-pressure stationary residual fails anywhere on the
slab then that exact velocity/pressure pair cannot be an honest finite-time
witness. -/
theorem
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
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
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  refine ⟨?_, ?_⟩
  · rcases boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields hν N L u₀ T with
      ⟨hsmooth, _hzero, hdiv, hinit, henergy⟩
    exact ⟨hsmooth, smoothSpaceTimePressure_timeOnly hπ, hdiv, hinit, henergy⟩
  · exact
      not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail

end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
