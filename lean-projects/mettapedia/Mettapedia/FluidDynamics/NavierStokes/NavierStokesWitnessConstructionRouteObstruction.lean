import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionBKMObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionUniformVorticityObstruction

/-!
# Witness-Construction Route Obstruction

This file packages the exact-pair repair surfaces currently formalized around
the witness-construction route. If a prescribed velocity/pressure pair already
fails the exact finite-time witness audit on one slab, then the same pair also
fails every packaged repair that keeps that velocity and pressure fixed:

* the exact finite-time witness surface,
* the same witness plus a uniform vorticity bound,
* the same witness plus BKM envelope data, and
* the prescribed-velocity exact whole-space output surface.

We then specialize this route-level obstruction to the boxed steady seed with
smooth zero-spatial-gradient pressure gauges, including the manuscript-facing
time-only subcase.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The currently formalized exact-pair witness-construction repair surfaces for
a prescribed velocity/pressure pair on a slab and the corresponding exact
whole-space output surface. Each branch keeps both the velocity and pressure
fixed in advance. -/
def ExactPairWitnessConstructionRoute
    (ν T : ℝ) (u₀ : NSInitialVelocity) (u : NSVelocityField) (p : NSPressureField) :
    Prop :=
  (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧ W.pressure = p) ∨
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧ W.pressure = p ∧
        ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ∨
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧ W.pressure = p ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B) ∨
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p

/-- The fixed-pair exact global-output surface is stable under adding any
smooth pressure gauge with zero spatial gradient on each slice, since the
momentum equation only sees the spatial pressure gradient. -/
theorem ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u (p + q) := by
  rcases h with ⟨hu, hp, hmom, hdiv, hinit, hbd⟩
  refine ⟨hu, smoothSpaceTimePressure_add hp hq, ?_, hdiv, hinit, hbd⟩
  intro t x
  have hp' :
      DifferentiableAt ℝ (fun y : NSSpace => p t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
  have hq' :
      DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
  rw [spatialPressureGradient_add hp' hq', hq_zero]
  simpa using hmom t x

/-- The bundled exact-pair witness-construction route is stable under adding a
smooth pressure gauge with zero spatial gradient on each slice.  Each branch
keeps the velocity fixed, so the carried witness/global-output data transport
along the same harmless gauge change. -/
theorem ExactPairWitnessConstructionRoute.addPressureOfZeroSpatialGradient
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hRoute : ExactPairWitnessConstructionRoute ν T u₀ u p)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExactPairWitnessConstructionRoute ν T u₀ u (p + q) := by
  rcases hRoute with hExact | hRoute
  · rcases hExact with ⟨W, hWvel, hWpress⟩
    refine Or.inl ?_
    refine ⟨W.addPressureOfZeroSpatialGradient q hq hq_zero, ?_, ?_⟩
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWvel]
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWpress]
  rcases hRoute with hUniform | hRoute
  · rcases hUniform with ⟨W, hWvel, hWpress, B, hω⟩
    refine Or.inr <| Or.inl ?_
    refine ⟨W.addPressureOfZeroSpatialGradient q hq hq_zero, ?_, ?_, B, ?_⟩
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWvel]
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWpress]
    · exact W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω q hq hq_zero
  rcases hRoute with hBKM | hGlobal
  · refine Or.inr <| Or.inr <| Or.inl ?_
    rcases hBKM with ⟨W, hWvel, hWpress, Ω, B, hEnv, hInt⟩
    refine ⟨W.addPressureOfZeroSpatialGradient q hq hq_zero, ?_, ?_, Ω, B, ?_, ?_⟩
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWvel]
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient, hWpress]
    · simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hEnv
    · simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hInt
  · refine Or.inr <| Or.inr <| Or.inr ?_
    exact hGlobal.addPressureOfZeroSpatialGradient q hq hq_zero

/-- The bundled exact-pair witness-construction route depends only on the
pressure gauge modulo adding a smooth field with zero spatial gradient on each
slice. -/
theorem ExactPairWitnessConstructionRoute_iff_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExactPairWitnessConstructionRoute ν T u₀ u (p + q) ↔
      ExactPairWitnessConstructionRoute ν T u₀ u p := by
  constructor
  · intro hRoute
    have hq_neg_zero : ∀ t x, spatialPressureGradient (-q) t x = 0 := by
      intro t x
      simpa [hq_zero t x] using spatialPressureGradient_neg q t x
    simpa [add_assoc] using
      hRoute.addPressureOfZeroSpatialGradient
        (-q)
        (smoothSpaceTimePressure_neg hq)
        hq_neg_zero
  · intro hRoute
    exact hRoute.addPressureOfZeroSpatialGradient q hq hq_zero

/-- The bundled exact-pair witness-construction route is conservative: it
exists exactly when the prescribed velocity/pressure pair already exists as an
exact finite-time witness on the slab. The extra packaging layers add no new
fixed-pair inhabitants. -/
theorem ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField} :
    ExactPairWitnessConstructionRoute ν T u₀ u p ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p := by
  constructor
  · intro hRoute
    rcases hRoute with hExact | hRoute
    · exact hExact
    rcases hRoute with hUniform | hRoute
    · rcases hUniform with ⟨W, hWvel, hWpress, _B, _hω⟩
      exact ⟨W, hWvel, hWpress⟩
    rcases hRoute with hBKM | hGlobal
    · rcases hBKM with ⟨W, hWvel, hWpress, _Ω, _B, _hEnv, _hInt⟩
      exact ⟨W, hWvel, hWpress⟩
    · exact
        ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.implies_finiteTimeWitness
          (T := T) hGlobal
  · intro hW
    exact Or.inl hW

/-- A slabwise exact-witness obstruction already blocks every currently
formalized repair surface that keeps the same velocity/pressure pair fixed. -/
theorem not_ExactPairWitnessConstructionRoute_of_not_exists_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p : NSPressureField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u ∧ W.pressure = p) :
    ¬ ExactPairWitnessConstructionRoute ν T u₀ u p := by
  intro hRoute
  rcases hRoute with hExact | hRoute
  · exact hW hExact
  rcases hRoute with hUniform | hRoute
  · exact
      (not_exists_uniformVorticityData_of_not_exists_finiteTimeWitness hW)
        hUniform
  rcases hRoute with hBKM | hGlobal
  · exact (not_exists_BKMData_of_not_exists_finiteTimeWitness hW) hBKM
  · exact
      (not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
        (T := T) hW) hGlobal

/-- For the manuscript-style boxed steady seed with a smooth time-only pressure
gauge, a single zero-pressure stationary residual failure already blocks every
currently formalized exact-pair witness-construction repair surface. -/
theorem
    not_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_ExactPairWitnessConstructionRoute_of_not_exists_finiteTimeWitness
      (not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
        hν N L u₀ π ht0 htT hfail)

/-- For the manuscript-style boxed steady seed with a smooth time-only pressure
gauge, the bundled exact-pair route exists exactly when the zero-pressure
stationary momentum balance holds on the slab. -/
theorem
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      (fun t : NSTime => fun _ : NSSpace => π t) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  rw [ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness]
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T π hπ

/-- Any fixed smooth pressure gauge with zero spatial gradient leaves the
bundled exact-pair route at the same boxed steady-seed boundary: the route
exists exactly when the zero-pressure stationary momentum balance already
holds on the slab. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  rw [ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness]
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T p hp hp_zero

/-- Allowing an arbitrary smooth zero-spatial-gradient pressure gauge does not
enlarge the bundled fixed-pair route for the boxed steady seed: such a route
exists for some harmless gauge exactly when the zero-pressure stationary
momentum balance already holds on the slab. -/
theorem
    exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) :
    (∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          (∀ t x, spatialPressureGradient p t x = 0) ∧
          ExactPairWitnessConstructionRoute
            ν
            T
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  constructor
  · rintro ⟨p, hp, hp_zero, hRoute⟩
    rw [ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness] at hRoute
    exact
      (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
        hν N L u₀ T p hp hp_zero).1 hRoute
  · intro hstat
    refine ⟨fun _ : NSTime => fun _ : NSSpace => (0 : ℝ), ?_, ?_, ?_⟩
    · simpa using smoothSpaceTimePressure_const (0 : ℝ)
    · intro t x
      simpa using spatialPressureGradient_zero t x
    · rw [ExactPairWitnessConstructionRoute_iff_exists_finiteTimeWitness]
      exact
        (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
          hν N L u₀ T
          (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ))
          (by simpa using smoothSpaceTimePressure_const (0 : ℝ))
          (by
            intro t x
            simpa using spatialPressureGradient_zero t x)).2 hstat

/-- On the boxed steady-seed route, every smooth zero-spatial-gradient pressure
gauge is propositionally the same as the zero-pressure representative. This is
stronger than merely showing that some harmless gauge exists: the whole gauge
orbit collapses to one exact route value. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_zeroPressure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p ↔
      ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ)) := by
  have hzero :
      ((fun _ : NSTime => fun _ : NSSpace => (0 : ℝ)) + p) = p := by
    funext t x
    simp
  exact
    hzero ▸
      (ExactPairWitnessConstructionRoute_iff_addPressureOfZeroSpatialGradient
        (ν := ν)
        (T := T)
        (u₀ := (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity)
        (u := boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (p := fun _ : NSTime => fun _ : NSSpace => (0 : ℝ))
        p
        hp
        hp_zero)

/-- Consequently, once the zero-pressure stationary residual fails for the
boxed steady seed, no individual smooth zero-spatial-gradient pressure gauge
can rescue the bundled exact-pair route. -/
theorem
    not_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ExactPairWitnessConstructionRoute
      ν
      T
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
      (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
      p := by
  intro hRoute
  have hZero :
      ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun _ : NSTime => fun _ : NSSpace => (0 : ℝ)) :=
    (boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_zeroPressure
      hν N L u₀ T p hp hp_zero).1 hRoute
  exact
    (not_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
      hν N L u₀ (fun _ : NSTime => (0 : ℝ)) ht0 htT hfail)
      hZero

/-- A single failed zero-pressure stationary residual already rules out the
entire smooth zero-spatial-gradient pressure-repair class for the bundled
boxed steady-seed route. -/
theorem
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
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
          ExactPairWitnessConstructionRoute
            ν
            T
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
            (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
            p := by
  intro hExist
  have hstat :=
    (exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T).1 hExist
  exact hfail (hstat t x ht0 htT)

/-- Candidate-level route obstruction for a boxed steady seed with an arbitrary
smooth zero-spatial-gradient pressure gauge: the seed already carries the
finite-time and global non-momentum fields, but a single failed zero-pressure
stationary residual still blocks every currently formalized exact-pair repair
surface. -/
theorem
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_exhibits_nonMomentumFiniteTimeAndGlobalFields_without_exactPairWitnessConstructionRoute
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      ¬ ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        p := by
  rcases boxedPartialPeriodizationSteadySeed_nonMomentumFiniteTimeFields hν N L u₀ T with
    ⟨hVel, _hPressZero, hDiv, hInit, hEnergyUpTo⟩
  refine ⟨hVel, hp, hDiv, hInit, hEnergyUpTo, ?_, ?_⟩
  · exact boundedKineticEnergy_boxedPartialPeriodizationSteadySeed hν N L u₀
  · exact
      not_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_ExactPairWitnessConstructionRoute_of_stationaryMomentum_failure
        hν N L u₀ p hp hp_zero ht0 htT hfail

/-- Candidate-level route obstruction for the manuscript-style boxed steady
seed with a smooth time-only pressure gauge: the seed already carries the
finite-time and global non-momentum fields, but a single stationary residual
failure still blocks every currently formalized exact-pair repair surface. -/
theorem
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeAndGlobalFields_without_exactPairWitnessConstructionRoute
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T ∧
      boundedKineticEnergy
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      ¬ ExactPairWitnessConstructionRoute
        ν
        T
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν)
        (fun t : NSTime => fun _ : NSSpace => π t) := by
  rcases
      boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
        hν N L u₀ T π hπ ht0 htT hfail with
    ⟨hFiniteFields, hNoExact⟩
  rcases hFiniteFields with ⟨hVel, hPress, hDiv, hInit, hEnergyUpTo⟩
  refine ⟨hVel, hPress, hDiv, hInit, hEnergyUpTo, ?_, ?_⟩
  · exact boundedKineticEnergy_boxedPartialPeriodizationSteadySeed hν N L u₀
  · exact not_ExactPairWitnessConstructionRoute_of_not_exists_finiteTimeWitness hNoExact

end NavierStokes
end FluidDynamics
end Mettapedia
