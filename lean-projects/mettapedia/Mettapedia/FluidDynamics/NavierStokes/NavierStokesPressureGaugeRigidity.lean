import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionRouteObstruction

/-!
# Pressure Gauge Rigidity

This file records the converse side of the harmless pressure-gauge symmetry on
the exact witness/global-output surfaces.

For a fixed velocity on a fixed slab, changing the pressure preserves exact
witness existence exactly when the pressure difference has zero spatial
gradient on that slab.  Likewise, for a fixed whole-space output velocity, two
admitted pressures differ only by a globally zero-spatial-gradient gauge.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Slab-local pressure-gauge symmetry on exact finite-time witnesses: adding a
smooth pressure field whose spatial gradient vanishes on the certified slab
leaves the witness valid on that same slab.  Unlike the older global gauge
transport theorem, this version does not impose any off-slab restriction. -/
def ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradientOn
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero_on : ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient q t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T where
  velocity := W.velocity
  pressure := W.pressure + q
  smooth_velocity := W.smooth_velocity
  smooth_pressure := smoothSpaceTimePressure_add W.smooth_pressure hq
  momentum_equation_on := by
    intro t x ht0 htT
    have hp :
        DifferentiableAt ℝ (fun y : NSSpace => W.pressure t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice W.smooth_pressure t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    rw [spatialPressureGradient_add hp hq', hq_zero_on t x ht0 htT, add_zero]
    simpa using W.momentum_equation_on t x ht0 htT
  incompressible_on := W.incompressible_on
  initial_condition := W.initial_condition
  bounded_energy_on := W.bounded_energy_on

/-- If two exact finite-time witnesses carry the same velocity on the same
slab, then their spatial pressure gradients already agree everywhere on that
slab.  Thus any pressure repair for a fixed velocity is rigid modulo a
slab-local zero-spatial-gradient gauge. -/
theorem ExplicitFiniteTimeRegularityWitness.sameVelocity_implies_spatialPressureGradient_eq_on
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    {W₁ W₂ : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (hvel : W₁.velocity = W₂.velocity) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialPressureGradient W₁.pressure t x =
        spatialPressureGradient W₂.pressure t x := by
  intro t x ht0 htT
  have hmom₁ := W₁.momentum_equation_on t x ht0 htT
  have hmom₂ := W₂.momentum_equation_on t x ht0 htT
  rw [hvel] at hmom₁
  have hsum :
      timeVelocityDerivative W₂.velocity t x +
          spatialConvection W₂.velocity t x +
          spatialPressureGradient W₁.pressure t x =
        timeVelocityDerivative W₂.velocity t x +
          spatialConvection W₂.velocity t x +
          spatialPressureGradient W₂.pressure t x := by
    exact hmom₁.trans hmom₂.symm
  exact add_left_cancel hsum

/-- For a fixed velocity on a fixed slab, replacing one admitted exact-witness
pressure by another is possible exactly when the pressure difference has zero
spatial gradient on that slab.  This makes the exact slab surface depend only
on the pressure gauge modulo slab-local time-only freedom. -/
theorem exists_finiteTimeWitness_with_sameVelocity_pressure_iff_pressureDifference_zeroGradient_on
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    {u : NSVelocityField} {p q : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧ W.pressure = p)
    (hq : smoothSpaceTimePressure q) :
    (∃ W' : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W'.velocity = u ∧ W'.pressure = q) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient (q - p) t x = 0 := by
  constructor
  · intro hW'
    rcases hW with ⟨W₁, hW₁vel, hW₁press⟩
    rcases hW' with ⟨W₂, hW₂vel, hW₂press⟩
    intro t x ht0 htT
    have hp :
        DifferentiableAt ℝ (fun y : NSSpace => p t y) x := by
      simpa [hW₁press] using
        smoothSpaceTimePressure_differentiableAt_spatialSlice W₁.smooth_pressure t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    have hgrad_eq :
        spatialPressureGradient p t x = spatialPressureGradient q t x := by
      simpa [hW₁press, hW₂press] using
        (ExplicitFiniteTimeRegularityWitness.sameVelocity_implies_spatialPressureGradient_eq_on
          (W₁ := W₁) (W₂ := W₂) (hW₁vel.trans hW₂vel.symm) t x ht0 htT)
    rw [spatialPressureGradient_sub hq' hp, hgrad_eq, sub_self]
  · intro hzero
    rcases hW with ⟨W, hWvel, hWpress⟩
    have hp : smoothSpaceTimePressure p := by
      simpa [hWpress] using W.smooth_pressure
    refine
      ⟨W.addPressureOfZeroSpatialGradientOn (q - p) (smoothSpaceTimePressure_sub hq hp) hzero,
        ?_, ?_⟩
    · simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradientOn, hWvel]
    · ext t x
      simp [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradientOn, hWpress]

/-- If two fixed-pair exact whole-space outputs carry the same velocity, then
their spatial pressure gradients already agree everywhere.  Thus whole-space
pressure repairs for a fixed velocity are rigid modulo a global zero-gradient
gauge. -/
theorem
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.sameVelocity_implies_spatialPressureGradient_eq
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p q : NSPressureField}
    (h₁ : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p)
    (h₂ : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u q) :
    ∀ t x,
      spatialPressureGradient p t x = spatialPressureGradient q t x := by
  intro t x
  rcases h₁ with ⟨_hu₁, _hp₁, hmom₁, _hinc₁, _hinit₁, _hbd₁⟩
  rcases h₂ with ⟨_hu₂, _hp₂, hmom₂, _hinc₂, _hinit₂, _hbd₂⟩
  have hsum :
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient q t x := by
    exact (hmom₁ t x).trans (hmom₂ t x).symm
  exact add_left_cancel hsum

/-- Whole-space exact output with a fixed velocity can be retargeted to a new
pressure exactly when the pressure difference has zero spatial gradient
everywhere.  This is the global analogue of the slab-local exact witness gauge
rigidity theorem. -/
theorem
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_iff_pressureDifference_zeroGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} {p q : NSPressureField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p)
    (hq : smoothSpaceTimePressure q) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u q ↔
      ∀ t x, spatialPressureGradient (q - p) t x = 0 := by
  constructor
  · intro hqOut t x
    have hp :
        DifferentiableAt ℝ (fun y : NSSpace => p t y) x := by
      rcases h with ⟨_hu, hp, _hmom, _hinc, _hinit, _hbd⟩
      exact smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    have hgrad_eq :
        spatialPressureGradient p t x = spatialPressureGradient q t x :=
      h.sameVelocity_implies_spatialPressureGradient_eq hqOut t x
    rw [spatialPressureGradient_sub hq' hp, hgrad_eq, sub_self]
  · intro hzero
    rcases h with ⟨hu, hp, hmom, hinc, hinit, hbd⟩
    have hsub :
        smoothSpaceTimePressure (q - p) := smoothSpaceTimePressure_sub hq hp
    have hq_out :
        ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u (p + (q - p)) := by
      exact
        (show ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u p from
            ⟨hu, hp, hmom, hinc, hinit, hbd⟩).addPressureOfZeroSpatialGradient
          (q - p) hsub hzero
    have hpeq : p + (q - p) = q := by
      ext t x
      simp
    simpa [hpeq] using hq_out

end NavierStokes
end FluidDynamics
end Mettapedia
