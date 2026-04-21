import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Concrete Uniform-Vorticity Continuation Target

This file adds the first concrete continuation-criterion surface on top of the
literal `ℝ × ℝ^3` Navier--Stokes theorem statement.  It defines explicit
finite-time witnesses on a time slab, a concrete curl/vorticity operator, a
uniform vorticity bound on that slab, and a continuation target saying that such
a finite-time witness should extend to a global one.

The resulting theorem is still only a target: the actual continuation proof is
not provided here.  But the target is now stated directly on the explicit PDE
surface rather than through arbitrary predicates.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Uniform kinetic-energy control on the slab `0 ≤ t ≤ T`. -/
def boundedKineticEnergyUpTo (u : NSVelocityField) (T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → t ≤ T →
    MeasureTheory.Integrable (kineticEnergyDensity u t) ∧ kineticEnergyAt u t ≤ C

/-- Uniform vorticity bound on the slab `0 ≤ t ≤ T`. -/
def uniformVorticityBoundUpTo (u : NSVelocityField) (T B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ t x, 0 ≤ t → t ≤ T → ‖spatialVorticity u t x‖ ≤ B

/-- Explicit finite-time smooth Navier--Stokes witness on the slab `0 ≤ t ≤ T`.
-/
structure ExplicitFiniteTimeRegularityWitness
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) where
  velocity : NSVelocityField
  pressure : NSPressureField
  smooth_velocity : smoothSpaceTimeVelocity velocity
  smooth_pressure : smoothSpaceTimePressure pressure
  momentum_equation_on :
    ∀ t x, 0 ≤ t → t ≤ T →
      timeVelocityDerivative velocity t x + spatialConvection velocity t x +
          spatialPressureGradient pressure t x =
        ν • spatialLaplacian velocity t x
  incompressible_on :
    ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence velocity t x = 0
  initial_condition : MatchesInitialVelocity u₀ velocity
  bounded_energy_on : boundedKineticEnergyUpTo velocity T

/-- Fully explicit global-output proposition for the concrete NS theorem surface.
-/
def ExplicitConcreteNavierStokesGlobalOutput
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  ∃ u : NSVelocityField, ∃ p : NSPressureField,
    smoothSpaceTimeVelocity u ∧
    smoothSpaceTimePressure p ∧
    (∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) ∧
    (∀ t x, spatialDivergence u t x = 0) ∧
    MatchesInitialVelocity u₀ u ∧
    boundedKineticEnergy u

/-- A concrete explicit global output immediately yields the corresponding
unrepaired explicit whole-space regularity clause. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv
  exact h

/-- A concrete explicit global output also yields the repaired explicit
whole-space regularity clause, since the extra finite-energy hypothesis only
narrows the admissible input data. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv _hfinite
  exact h

/-- A concrete explicit global output can be repackaged directly as the
structured fully concrete clause on the same datum. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  exact
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr h

/-- On a finite-energy datum, a concrete explicit global output can likewise be
repackaged directly as the repaired structured fully concrete clause. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mpr
      (ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        h)

/-- Concrete uniform-vorticity continuation clause: a finite-time smooth witness
with bounded vorticity on `0 ≤ t ≤ T` extends to a global smooth witness. -/
def ExplicitUniformVorticityContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          (∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) →
            ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global continuation target built from the concrete uniform-vorticity clause.
-/
def ExplicitUniformVorticityContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitUniformVorticityContinuationClause ν u₀ T

/-- Repaired uniform-vorticity continuation clause: the concrete continuation
surface is restricted to smooth divergence-free initial data with finite
initial kinetic energy on `ℝ^3`. -/
def ExplicitFiniteEnergyUniformVorticityContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
          ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
            (∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) →
              ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global repaired continuation target built from the finite-energy
uniform-vorticity clause. -/
def ExplicitFiniteEnergyUniformVorticityContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T

/-- Corrected repaired continuation target: only nonnegative horizons are
admissible. This rules out the degenerate negative-horizon witness loophole
while retaining the intended finite-energy continuation surface. -/
def ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ ⦃T : ℝ⦄,
    0 ≤ T → ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T

/-- The repaired uniform-vorticity continuation clause is vacuous outside the
finite-energy input domain: once `u₀` fails the repaired hypothesis, the clause
holds for purely logical reasons. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro _hν _hsmooth _hdiv hE _W _hω
  exact False.elim (hfinite hE)

/-- Direct zero-field uniform vorticity bound on every slab. -/
theorem uniformVorticityBoundUpTo_zero
    (T : ℝ) :
    uniformVorticityBoundUpTo (0 : NSVelocityField) T 0 := by
  constructor
  · exact le_rfl
  · intro t x ht0 htT
    simp [spatialVorticity_zero]

/-- Constant velocity fields carry the explicit zero vorticity bound on every
slab.  This is a real differential-side nonzero family, although it will later
be blocked by the bounded-energy surface unless the constant is zero. -/
theorem uniformVorticityBoundUpTo_constantVelocityField
    (c : NSSpace) (T : ℝ) :
    uniformVorticityBoundUpTo (constantVelocityField c) T 0 := by
  constructor
  · exact le_rfl
  · intro t x ht0 htT
    simp [spatialVorticity_constantVelocityField]

/-- The steady linear shear field carries the explicit constant vorticity bound
`B = |a|` on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearVelocityField
    (a T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVelocityField a) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearVelocityField]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField
    (a b T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVerticalDriftVelocityField a b) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearVerticalDriftVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField
    (a b T : ℝ) :
    uniformVorticityBoundUpTo (linearShearHorizontalDriftVelocityField a b) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearHorizontalDriftVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, c)` carries the same explicit
constant vorticity bound `B = |a|` as pure linear shear on every slab. -/
theorem uniformVorticityBoundUpTo_linearShearFullDriftVelocityField
    (a b c T : ℝ) :
    uniformVorticityBoundUpTo (linearShearFullDriftVelocityField a b c) T |a| := by
  constructor
  · exact abs_nonneg a
  · intro t x ht0 htT
    simp [spatialVorticity_linearShearFullDriftVelocityField]

/-- The damped sinusoidal heat-shear field carries the explicit slab vorticity
bound `B = |a * k|` whenever the viscosity is nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearVelocityField
    (ν a k T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearVelocityField ν a k) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with constant streamwise drift carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField
    (ν a k d T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearStreamwiseDriftVelocityField ν a k d) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearStreamwiseDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with vertical drift carries the same slab vorticity
bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField
    (ν a k c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearVerticalDriftVelocityField ν a k c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearVerticalDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The heat-shear family with full constant drift carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearFullDriftVelocityField
    (ν a k d c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearFullDriftVelocityField ν a k d c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearFullDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |Real.cos (k * x nsCoord1)| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * x nsCoord1)| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * x nsCoord1)
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The transported heat-shear family carries the same slab vorticity bound
`B = |a * k|` as pure heat shear whenever the viscosity is nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearTransportVelocityField
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearTransportVelocityField ν a k b) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearTransportVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.cos (k * (x nsCoord1 - b * t)) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- The transported full-drift heat-shear family carries the same slab
vorticity bound `B = |a * k|` as pure heat shear whenever the viscosity is
nonnegative. -/
theorem uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν) :
    uniformVorticityBoundUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T |a * k| := by
  constructor
  · exact abs_nonneg (a * k)
  · intro t x ht0 htT
    rw [spatialVorticity_heatShearTransportFullDriftVelocityField]
    have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
      nlinarith
    calc
      ‖EuclideanSpace.single nsCoord2
          (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.cos (k * (x nsCoord1 - b * t)) * k))‖
          = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |a| * 1 * |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
            gcongr
      _ ≤ |a| * 1 * 1 * |k| := by
            gcongr
            simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
      _ = |a * k| := by
            rw [abs_mul]
            ring

/-- Uniform slab vorticity bounds are stable under constant velocity rescaling:
if `‖ω_u‖ ≤ B`, then `‖ω_{a•u}‖ ≤ |a| * B` on the same slab. -/
theorem uniformVorticityBoundUpTo_const_smul
    {u : NSVelocityField} {T B : ℝ}
    (a : ℝ)
    (hω : uniformVorticityBoundUpTo u T B) :
    uniformVorticityBoundUpTo (a • u) T (|a| * B) := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact mul_nonneg (abs_nonneg a) hB
  · intro t x ht0 htT
    have hωtx : ‖spatialVorticity u t x‖ ≤ B := hbound t x ht0 htT
    have hsmul :
        spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
      ext i
      fin_cases i <;>
        simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]
    rw [hsmul]
    calc
      ‖a • spatialVorticity u t x‖ = ‖a‖ * ‖spatialVorticity u t x‖ := by
        simp [norm_smul]
      _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left hωtx (norm_nonneg a)
      _ = |a| * B := by simp [Real.norm_eq_abs]

/-- Uniform slab vorticity bounds are monotone in the bound parameter. -/
theorem uniformVorticityBoundUpTo_mono
    {u : NSVelocityField} {T B B' : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hBB' : B ≤ B') :
    uniformVorticityBoundUpTo u T B' := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact le_trans hB hBB'
  · intro t x ht0 htT
    exact le_trans (hbound t x ht0 htT) hBB'

/-- Uniform slab vorticity bounds add for smooth space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_add
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    uniformVorticityBoundUpTo (u + v) T (B + B') := by
  rcases hω with ⟨hB, hbound⟩
  rcases hω' with ⟨hB', hbound'⟩
  constructor
  · exact add_nonneg hB hB'
  · intro t x ht0 htT
    rw [spatialVorticity_add
      (u := u) (v := v) (t := t) (x := x)
      (smoothSpaceTimeVelocity_differentiableAt_spatialSlice hu t x)
      (smoothSpaceTimeVelocity_differentiableAt_spatialSlice hv t x)]
    calc
      ‖spatialVorticity u t x + spatialVorticity v t x‖ ≤
          ‖spatialVorticity u t x‖ + ‖spatialVorticity v t x‖ := norm_add_le _ _
      _ ≤ B + B' := add_le_add (hbound t x ht0 htT) (hbound' t x ht0 htT)

/-- Uniform slab vorticity bounds are stable under sign flip of the velocity
field. -/
theorem uniformVorticityBoundUpTo_neg
    {u : NSVelocityField} {T B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B) :
    uniformVorticityBoundUpTo (-u) T B := by
  have hsmul :
      uniformVorticityBoundUpTo ((-1 : ℝ) • u) T (|(-1 : ℝ)| * B) :=
    uniformVorticityBoundUpTo_const_smul (a := (-1 : ℝ)) hω
  simpa using hsmul

/-- Uniform slab vorticity bounds are stable under subtraction for smooth
space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_sub
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    uniformVorticityBoundUpTo (u - v) T (B + B') := by
  simpa [sub_eq_add_neg] using
    (uniformVorticityBoundUpTo_add
      (u := u) (v := -v) (T := T) (B := B) (B' := B')
      hu (smoothSpaceTimeVelocity_neg hv) hω (uniformVorticityBoundUpTo_neg hω'))

/-- Uniform slab vorticity bounds are stable under linear combinations for
smooth space-time velocity fields. -/
theorem uniformVorticityBoundUpTo_linearCombination
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    uniformVorticityBoundUpTo (a • u + b • v) T (|a| * B + |b| * B') := by
  exact
    uniformVorticityBoundUpTo_add
      (u := a • u) (v := b • v) (T := T)
      (B := |a| * B) (B' := |b| * B')
      (smoothSpaceTimeVelocity_const_smul a hu)
      (smoothSpaceTimeVelocity_const_smul b hv)
      (uniformVorticityBoundUpTo_const_smul (a := a) hω)
      (uniformVorticityBoundUpTo_const_smul (a := b) hω')

/-- Uniform slab vorticity bounds restrict from a larger time horizon `T` to
any smaller one `T' ≤ T`. -/
theorem uniformVorticityBoundUpTo_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo u T' B := by
  rcases hω with ⟨hB, hbound⟩
  constructor
  · exact hB
  · intro t x ht0 htT'
    exact hbound t x ht0 (le_trans htT' hT)

/-- Uniform slab kinetic-energy bounds restrict from a larger time horizon `T`
to any smaller one `T' ≤ T`. -/
theorem boundedKineticEnergyUpTo_restrict
    {u : NSVelocityField} {T T' : ℝ}
    (hE : boundedKineticEnergyUpTo u T)
    (hT : T' ≤ T) :
    boundedKineticEnergyUpTo u T' := by
  rcases hE with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht0 htT'
  exact hbound t ht0 (le_trans htT' hT)

/-- Restrict an explicit finite-time witness from a slab `0 ≤ t ≤ T` to any
shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
def ExplicitFiniteTimeRegularityWitness.restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hT : T' ≤ T) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T' where
  velocity := W.velocity
  pressure := W.pressure
  smooth_velocity := W.smooth_velocity
  smooth_pressure := W.smooth_pressure
  momentum_equation_on := by
    intro t x ht0 htT'
    exact W.momentum_equation_on t x ht0 (le_trans htT' hT)
  incompressible_on := by
    intro t x ht0 htT'
    exact W.incompressible_on t x ht0 (le_trans htT' hT)
  initial_condition := W.initial_condition
  bounded_energy_on := boundedKineticEnergyUpTo_restrict W.bounded_energy_on hT

/-- Uniform slab vorticity control transports along witness restriction. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo (W.restrict hT).velocity T' B := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)

/-- Witness-level transport of uniform vorticity control under linear
combination of slab velocities. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ) :
    uniformVorticityBoundUpTo (a • W.velocity + b • W'.velocity) T (|a| * B + |b| * B') := by
  exact uniformVorticityBoundUpTo_linearCombination
    W.smooth_velocity W'.smooth_velocity hω hω' a b

/-- Witness-level transport of uniform vorticity control under linear
combination followed by restriction to a shorter slab `0 ≤ t ≤ T'` with
`T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo
      (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T'
      (|a| * B + |b| * B') := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict
      (u := a • W.velocity + b • W'.velocity) (T := T) (T' := T')
      (B := |a| * B + |b| * B')
      (W.uniformVorticityBound_linearCombination W' hω hω' a b) hT)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied to
any larger-slab witness by restricting the witness and its uniform bound from
`0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo (W.restrict hT).velocity T' B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_restrict hω hT
  exact hClause hν hsmooth hdiv (W.restrict hT) hω'

/-- Horizon monotonicity for the uniform-vorticity continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting any larger-slab witness to the smaller slab. -/
theorem ExplicitUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitUniformVorticityContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv W hω
  rcases hω with ⟨B, hbound⟩
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
      hClauseSmall hν hsmooth hdiv W hbound hT

/-- The repaired uniform-vorticity continuation clause at horizon `T'` can be
applied to any larger-slab witness by restricting the witness and its uniform
bound from `0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo (W.restrict hT).velocity T' B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_restrict hω hT
  exact hClause hν hsmooth hdiv hfinite (W.restrict hT) hω'

/-- Horizon monotonicity for the repaired uniform-vorticity continuation
clause: if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it
is also available on every larger slab `0 ≤ t ≤ Tlarge` with
`Tsmall ≤ Tlarge`, by restricting any larger-slab witness to the smaller slab.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv hfinite W hω
  rcases hω with ⟨B, hbound⟩
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_apply_of_uniformVorticityBound_restrict
      hClauseSmall hν hsmooth hdiv hfinite W hbound hT

/-- A global bounded-energy witness immediately restricts to a bounded-energy
witness on every finite time slab. -/
theorem boundedKineticEnergy_implies_boundedKineticEnergyUpTo
    {u : NSVelocityField} {T : ℝ}
    (h : boundedKineticEnergy u) :
    boundedKineticEnergyUpTo u T := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht0 htT
  exact hbound t

/-- Matching the initial condition identifies the explicit initial kinetic
energy density with the time-zero kinetic-energy density of the space-time
field. -/
theorem initialKineticEnergyDensity_eq_of_matchesInitialVelocity
    {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hinit : MatchesInitialVelocity u₀ u) :
    initialKineticEnergyDensity u₀ = kineticEnergyDensity u 0 := by
  funext x
  simp [initialKineticEnergyDensity, kineticEnergyDensity, hinit x]

/-- On a nonnegative slab, any bounded-energy witness already forces finite
initial kinetic energy for the prescribed datum. -/
theorem finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
    {u₀ : NSInitialVelocity} {u : NSVelocityField} {T : ℝ}
    (hinit : MatchesInitialVelocity u₀ u)
    (hE : boundedKineticEnergyUpTo u T)
    (hT : 0 ≤ T) :
    finiteInitialKineticEnergy u₀ := by
  rcases hE with ⟨C, hC, hbound⟩
  have hInt0 : MeasureTheory.Integrable (kineticEnergyDensity u 0) := (hbound 0 le_rfl hT).1
  rw [finiteInitialKineticEnergy, initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit]
  exact hInt0

/-- Therefore every explicit finite-time regularity witness on a nonnegative
slab carries finite initial kinetic energy. -/
theorem ExplicitFiniteTimeRegularityWitness.finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hT : 0 ≤ T) :
    finiteInitialKineticEnergy u₀ := by
  exact
    finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
      W.initial_condition W.bounded_energy_on hT

/-- Conversely, if the initial datum fails the finite-energy input condition,
then the explicit finite-time witness type is empty on every nonnegative slab.
-/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hfinite : ¬ finiteInitialKineticEnergy u₀)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact hfinite (W.finiteInitialKineticEnergy hT)

/-- Kinetic-energy density of a constant velocity field is a positive constant
function on space. -/
theorem kineticEnergyDensity_constantVelocityField
    (c : NSSpace) (t : NSTime) :
    kineticEnergyDensity (constantVelocityField c) t = fun _ : NSSpace => ‖c‖ ^ (2 : ℕ) := by
  funext x
  simp [kineticEnergyDensity, constantVelocityField]

/-- A nonzero constant velocity field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density. -/
theorem not_integrable_kineticEnergyDensity_constantVelocityField
    {c : NSSpace} (hc : c ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) t) := by
  have hconst : (‖c‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hnotfinite :
      ¬ MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.not_isFiniteMeasure_iff]
    exact MeasureTheory.measure_univ_of_isAddLeftInvariant
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
  intro hInt
  have hfinite :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [kineticEnergyDensity_constantVelocityField c t] at hInt
    exact (MeasureTheory.integrable_const_iff_isFiniteMeasure hconst).mp hInt
  exact hnotfinite hfinite

/-- Therefore a nonzero constant velocity field never satisfies the concrete
global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_constantVelocityField
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0 (hbound 0).1

/-- On every nonnegative slab, a nonzero constant velocity field also fails the
finite-time bounded-energy predicate.  This records the honest obstruction that
blocks the tempting constant-field witness ansatz on `ℝ^3`. -/
theorem not_boundedKineticEnergyUpTo_constantVelocityField
    {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (constantVelocityField c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0
    ((hbound 0 le_rfl hT).1)

/-- If a velocity field matches nonzero constant initial data at time `0`, then
its initial kinetic-energy density agrees with the constant-field one. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    kineticEnergyDensity u 0 = kineticEnergyDensity (constantVelocityField c) 0 := by
  funext x
  simp [kineticEnergyDensity, constantVelocityField, constantInitialVelocity, hinit x]

/-- Therefore any velocity field matching nonzero constant initial data already
fails the integrability requirement at time `0`. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hc : c ≠ 0)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntConst :
      MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) 0) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_constantInitialVelocity hinit] using hInt
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0 hIntConst

/-- Hence any nonnegative finite-time slab witness with nonzero constant initial
data is blocked by the bounded-energy slot, regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
      hc hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out the global bounded-energy predicate for any
velocity field with nonzero constant initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_constantInitialVelocity
    {u : NSVelocityField} {c : NSSpace}
    (hc : c ≠ 0)
    (hinit : MatchesInitialVelocity (constantInitialVelocity c) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_constantInitialVelocity
      hc hinit ((hbound 0).1)

/-- Nonzero constant initial data are therefore not finite-energy admissible on
`ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_constantInitialVelocity
    {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ finiteInitialKineticEnergy (constantInitialVelocity c) := by
  intro hE
  have hIntConst :
      MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) 0) := by
    simpa [finiteInitialKineticEnergy, initialKineticEnergyDensity,
      constantVelocityField, constantInitialVelocity] using hE
  exact not_integrable_kineticEnergyDensity_constantVelocityField hc 0 hIntConst

/-- Therefore the repaired structured whole-space input domain contains no
problem datum whose initial velocity is a nonzero constant field. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_constantInitialVelocity
    {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = constantInitialVelocity c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- Therefore the explicit finite-time witness type is uninhabited on any
nonnegative slab for nonzero constant initial data. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_constantInitialVelocity
      (u := W.velocity) hc hT W.initial_condition W.bounded_energy_on

/-- Any explicit slab candidate with a uniform-vorticity bound and missing only
the bounded-energy slot remains such a candidate after adding a smooth
slice-wise zero-spatial-gradient pressure gauge. The velocity, vorticity
control, initial matching, and bounded-energy obstruction are unchanged. -/
theorem exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (h :
      ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
        smoothSpaceTimeVelocity u ∧
        smoothSpaceTimePressure p ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x) ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
        MatchesInitialVelocity u₀ u ∧
        uniformVorticityBoundUpTo u T B ∧
        ¬ boundedKineticEnergyUpTo u T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases h with ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  refine ⟨u, p + q, B, hu, smoothSpaceTimePressure_add hp hq, ?_, hdiv, hinit, hω, hE⟩
  intro t x ht0 htT
  have hp' : DifferentiableAt ℝ (fun y : NSSpace => p t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
  have hq' : DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
  exact
    momentumEquation_addPressureOfZeroSpatialGradient
      (u := u) (p := p) (q := q) hp' hq' (hq_zero t x) (hmom t x ht0 htT)

/-- A nonzero constant velocity field is an exact smooth incompressible
Navier--Stokes candidate on every nonnegative slab, with the explicit uniform
zero vorticity bound; the only missing finite-time witness slot is bounded
kinetic energy on `ℝ^3`. -/
theorem constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨constantVelocityField c, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_constantVelocityField c
  · simpa using smoothSpaceTimePressure_const (0 : ℝ)
  · intro t x ht0 htT
    simp [timeVelocityDerivative_constantVelocityField,
      spatialConvection_constantVelocityField, spatialPressureGradient_zero,
      spatialLaplacian_constantVelocityField]
  · intro t x ht0 htT
    simpa using spatialDivergence_constantVelocityField c t x
  · exact matchesInitialVelocity_constantVelocityField c
  · exact uniformVorticityBoundUpTo_constantVelocityField c T
  · exact not_boundedKineticEnergyUpTo_constantVelocityField hc hT

/-- The same nonzero constant-field slab candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge. The honest
obstruction on `ℝ^3` is still only the bounded-energy slot. -/
theorem constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (u₀ := constantInitialVelocity c)
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (c := c) hc hT)
      q hq hq_zero

/-- Constant initial data expose the same honest gap on the concrete
uniform-vorticity surface as the shear families: there is an exact smooth
incompressible slab candidate with uniform zero vorticity, but the finite-time
witness type is empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) hc hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- The same honest constant-data gap persists after adding any smooth
zero-spatial-gradient pressure gauge to the explicit constant-field slab
candidate. -/
theorem constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact
      constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) hc hT q hq hq_zero
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- If the concrete finite-time witness type is empty on a slab, then the
uniform-vorticity continuation clause is true there only vacuously. -/
theorem ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hEmpty : ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T)) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hω
  exfalso
  exact hEmpty ⟨W⟩

/-- The fully explicit global-output surface is likewise impossible for nonzero
constant initial data, independent of what pressure field is used later. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (constantInitialVelocity c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_constantInitialVelocity
      (u := u) hc hinit hbd

/-- At positive viscosity, the concrete global-regularity clause is therefore
also impossible for nonzero constant initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (constantInitialVelocity c) :=
    smoothInitialVelocityData_constantInitialVelocity c
  have hdiv : ∀ x, initialSpatialDivergence (constantInitialVelocity c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_constantInitialVelocity c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity hc
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The repaired explicit regularity clause is vacuous on nonzero constant
initial data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (constantInitialVelocity c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired explicit regularity clause can therefore be true on nonzero
constant initial data while the unrepaired concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_without_regularity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (constantInitialVelocity c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity
      (ν := ν) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The structured fully concrete clause also rejects nonzero constant initial
data.  This is the same obstruction as on the explicit surface, transported
through the concrete equivalence theorem. -/
theorem not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity c
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_constantInitialVelocity c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity hc
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := constantInitialVelocity c)
        hν
        (smoothInitialVelocityData_constantInitialVelocity c)
        (by
          intro x
          simpa using initialSpatialDivergence_constantInitialVelocity c x)).mp hClause)

/-- Kinetic-energy density carried by the linear shear initial profile
`x ↦ (a * x₁, 0, 0)`. -/
def linearShearKineticEnergyDensity (a : ℝ) : NSSpace → ℝ :=
  fun x => (a * x nsCoord1) * (a * x nsCoord1)

/-- The linear shear kinetic-energy density is continuous on `ℝ^3`. -/
theorem continuous_linearShearKineticEnergyDensity
    (a : ℝ) :
    Continuous (linearShearKineticEnergyDensity a) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  exact (continuous_const.mul hcoord).mul (continuous_const.mul hcoord)

/-- Nonzero linear shear initial data have nonintegrable kinetic-energy density
on `ℝ^3`.  The proof uses the exact Haar-scaling identity on `ℝ^3`: if this
density were integrable, scaling by `x ↦ 2x` would force its integral to be
both `4I` and `I/8`, hence zero, contradicting positivity. -/
theorem not_integrable_linearShearKineticEnergyDensity
    {a : ℝ} (ha : a ≠ 0) :
    ¬ MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
  intro hInt
  let x1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  have hnonneg : ∀ x, 0 ≤ linearShearKineticEnergyDensity a x := by
    intro x
    dsimp [linearShearKineticEnergyDensity]
    nlinarith [sq_nonneg (a * x nsCoord1)]
  have hx1 : linearShearKineticEnergyDensity a x1 ≠ 0 := by
    dsimp [x1, linearShearKineticEnergyDensity]
    simp [nsCoord1, ha]
  have hpos : 0 < ∫ x, linearShearKineticEnergyDensity a x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x1)
      (continuous_linearShearKineticEnergyDensity a)
      hInt hnonneg hx1
  let I : ℝ := ∫ x, linearShearKineticEnergyDensity a x
  have hcomp :
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x) = (4 : ℝ) * I := by
    calc
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x)
          = ∫ x, (4 : ℝ) * linearShearKineticEnergyDensity a x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [linearShearKineticEnergyDensity]
              ring
      _ = (4 : ℝ) * I := by
            simp [I, MeasureTheory.integral_const_mul]
  have hchange :
      ∫ x, linearShearKineticEnergyDensity a ((2 : ℝ) • x) =
        ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    simpa [smul_eq_mul, I] using
      (MeasureTheory.Measure.integral_comp_smul_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
        (f := linearShearKineticEnergyDensity a) (R := (2 : ℝ)) (hR := by positivity))
  have hEq :
      (4 : ℝ) * I = ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    rw [← hcomp]
    exact hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  have : 0 < I := by
    simpa [I] using hpos
  linarith

/-- Kinetic-energy density of the steady linear shear field is exactly the
quadratic shear profile on every time slice. -/
theorem kineticEnergyDensity_linearShearVelocityField
    (a : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearVelocityField a) t =
      linearShearKineticEnergyDensity a := by
  funext x
  rw [kineticEnergyDensity, linearShearVelocityField, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- A steady linear shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearVelocityField
    {a : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (linearShearVelocityField a) t) := by
  intro hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [kineticEnergyDensity_linearShearVelocityField a t] using hInt
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady linear shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearVelocityField
    {a : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearVelocityField a) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVelocityField
      (a := a) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady linear shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearVelocityField
    {a T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearVelocityField a) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVelocityField
      (a := a) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
0, b)` is the linear-shear density plus the constant drift contribution `b²`
on every time slice. -/
theorem kineticEnergyDensity_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearVerticalDriftVelocityField a b) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearVerticalDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- A steady affine shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearVerticalDriftVelocityField a b) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearVerticalDriftVelocityField a b t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearVerticalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearVerticalDriftVelocityField a b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearVerticalDriftVelocityField
    {a b T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearVerticalDriftVelocityField a b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
b, 0)` is the linear-shear density plus the constant drift contribution `b²`
on every time slice. -/
theorem kineticEnergyDensity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearHorizontalDriftVelocityField a b) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearHorizontalDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- A steady affine shear field with nonzero shear coefficient is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearHorizontalDriftVelocityField a b) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearHorizontalDriftVelocityField a b t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with nonzero shear coefficient never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearHorizontalDriftVelocityField
    {a b : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearHorizontalDriftVelocityField a b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with nonzero shear
coefficient also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearHorizontalDriftVelocityField
    {a b T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearHorizontalDriftVelocityField a b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha 0 ((hbound 0 le_rfl hT).1)

/-- Kinetic-energy density of the steady affine shear field `u(t,x) = (a * x₁,
b, c)` is the linear-shear density plus the constant drift contribution
`b² + c²` on every time slice. -/
theorem kineticEnergyDensity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) :
    kineticEnergyDensity (linearShearFullDriftVelocityField a b c) t =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, linearShearFullDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- A steady affine shear field with full constant drift and nonzero shear
coefficient is not spatially integrable on `ℝ^3` with respect to the
kinetic-energy density on any time slice. -/
theorem not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
    {a b c : ℝ} (ha : a ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (linearShearFullDriftVelocityField a b c) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_linearShearFullDriftVelocityField a b c t] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Therefore a steady affine shear field with full constant drift and nonzero
shear coefficient never satisfies the concrete global bounded-energy predicate
on `ℝ^3`. -/
theorem not_boundedKineticEnergy_linearShearFullDriftVelocityField
    {a b c : ℝ} (ha : a ≠ 0) :
    ¬ boundedKineticEnergy (linearShearFullDriftVelocityField a b c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha 0 (hbound 0).1

/-- On every nonnegative slab, a steady affine shear field with full constant
drift and nonzero shear coefficient also fails the finite-time bounded-energy
predicate. -/
theorem not_boundedKineticEnergyUpTo_linearShearFullDriftVelocityField
    {a b c T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (linearShearFullDriftVelocityField a b c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha 0 ((hbound 0 le_rfl hT).1)

/-- If a velocity field matches linear shear initial data at time `0`, then its
initial kinetic-energy density is exactly the linear shear density. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    kineticEnergyDensity u 0 = linearShearKineticEnergyDensity a := by
  funext x
  rw [kineticEnergyDensity, hinit x, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- The initial kinetic-energy density of linear shear is exactly the same
quadratic profile used in the time-zero obstruction lemmas above. -/
theorem initialKineticEnergyDensity_linearShearInitialVelocity
    (a : ℝ) :
    initialKineticEnergyDensity (linearShearInitialVelocity a) =
      linearShearKineticEnergyDensity a := by
  funext x
  rw [initialKineticEnergyDensity, linearShearInitialVelocity_apply]
  simpa [linearShearKineticEnergyDensity, pow_two] using
    (sq_abs (a * x nsCoord1))

/-- Therefore any velocity field matching nonzero linear shear initial data
already fails the integrability requirement at time `0`. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearInitialVelocity hinit]
      using hInt
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, 0, b)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    kineticEnergyDensity u 0 = fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  have hb : ‖b‖ ^ (2 : ℕ) = b ^ (2 : ℕ) := by
    simp [pow_two]
  rw [kineticEnergyDensity, hinit x, linearShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, 0, b)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, b, 0)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    kineticEnergyDensity u 0 = fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, hinit x, linearShearHorizontalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, b, 0)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- If a velocity field matches the initial data `x ↦ (a * x₁, b, c)` at time
`0`, then its time-zero kinetic-energy density is the linear-shear density plus
the constant drift contribution `b² + c²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    kineticEnergyDensity u 0 =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [kineticEnergyDensity, hinit x, linearShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nonzero initial data
`x ↦ (a * x₁, b, c)` already fails the integrability requirement at time `0`.
-/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      hinit] using hInt
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Nonzero linear shear initial data are therefore not finite-energy
admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearInitialVelocity
    {a : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity a) := by
  intro hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearInitialVelocity a] using hE
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, 0, b)` is the linear-shear density plus the constant drift term
`b²`. -/
theorem initialKineticEnergyDensity_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) :
    initialKineticEnergyDensity (linearShearVerticalDriftInitialVelocity a b) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  have hb : ‖b‖ ^ (2 : ℕ) = b ^ (2 : ℕ) := by
    simp [pow_two]
  rw [initialKineticEnergyDensity, linearShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, 0, b)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a b) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearVerticalDriftInitialVelocity a b] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, b, 0)` is the linear-shear density plus the constant drift term
`b²`. -/
theorem initialKineticEnergyDensity_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) :
    initialKineticEnergyDensity (linearShearHorizontalDriftInitialVelocity a b) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [initialKineticEnergyDensity, linearShearHorizontalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearHorizontalDriftInitialVelocity a b] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- The initial kinetic-energy density of the affine shear datum
`x ↦ (a * x₁, b, c)` is the linear-shear density plus the constant drift term
`b² + c²`. -/
theorem initialKineticEnergyDensity_linearShearFullDriftInitialVelocity
    (a b c : ℝ) :
    initialKineticEnergyDensity (linearShearFullDriftInitialVelocity a b c) =
      fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  have hs : (|a| * |x.ofLp 1|) ^ (2 : ℕ) = linearShearKineticEnergyDensity a x := by
    rw [linearShearKineticEnergyDensity]
    calc
      (|a| * |x.ofLp 1|) ^ (2 : ℕ) = |a * x.ofLp 1| ^ (2 : ℕ) := by rw [abs_mul]
      _ = a * x.ofLp 1 * (a * x.ofLp 1) := by
        simpa [pow_two] using (sq_abs (a * x.ofLp 1))
  rw [initialKineticEnergyDensity, linearShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Nonzero affine shear initial data `x ↦ (a * x₁, b, c)` are likewise not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
    {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => linearShearKineticEnergyDensity a x + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_linearShearFullDriftInitialVelocity a b c] using hE
  have hIntShear : MeasureTheory.Integrable (linearShearKineticEnergyDensity a) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_linearShearKineticEnergyDensity a).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ linearShearKineticEnergyDensity a x := by
      dsimp [linearShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * x nsCoord1)]
    rw [Real.norm_of_nonneg hx]
    have hbc : 0 ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
    nlinarith
  exact not_integrable_linearShearKineticEnergyDensity ha hIntShear

/-- Kinetic-energy density carried by the heat-shear initial profile
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
def heatShearKineticEnergyDensity (a k : ℝ) : NSSpace → ℝ :=
  fun x => (a * Real.sin (k * x nsCoord1)) * (a * Real.sin (k * x nsCoord1))

/-- The heat-shear kinetic-energy density is continuous on `ℝ^3`. -/
theorem continuous_heatShearKineticEnergyDensity
    (a k : ℝ) :
    Continuous (heatShearKineticEnergyDensity a k) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  have hsin : Continuous fun x : NSSpace => Real.sin (k * x nsCoord1) := by
    simpa [mul_assoc] using Real.continuous_sin.comp (continuous_const.mul hcoord)
  exact (continuous_const.mul hsin).mul (continuous_const.mul hsin)

/-- An anisotropic scaling that expands only the `x₀` and `x₂` directions by
`2`, leaving the heat-shear density unchanged while multiplying Haar measure by
`1 / 4`. -/
def heatShearLateralScaling : NSSpace →ₗ[ℝ] NSSpace :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(2 : ℝ), 1, 2])

/-- The heat-shear lateral scaling fixes the `x₁` coordinate. -/
theorem heatShearLateralScaling_apply_coord1
    (x : NSSpace) :
    heatShearLateralScaling x nsCoord1 = x nsCoord1 := by
  rw [heatShearLateralScaling, Matrix.toLpLin_apply]
  simp [Matrix.mulVec, nsCoord1]

/-- The heat-shear kinetic-energy density is invariant under the lateral
scaling that stretches only `x₀` and `x₂`. -/
theorem heatShearKineticEnergyDensity_comp_heatShearLateralScaling
    (a k : ℝ) :
    (fun x => heatShearKineticEnergyDensity a k (heatShearLateralScaling x)) =
      heatShearKineticEnergyDensity a k := by
  funext x
  simp [heatShearKineticEnergyDensity, heatShearLateralScaling_apply_coord1]

/-- The lateral-scaling determinant is `4`. -/
theorem det_heatShearLateralScaling :
    LinearMap.det heatShearLateralScaling = 4 := by
  rw [heatShearLateralScaling, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_three]
  have h0 : (![2, 1, 2] (0 : Fin 3) : ℝ) = 2 := by rfl
  have h1 : (![2, 1, 2] (1 : Fin 3) : ℝ) = 1 := by rfl
  have h2 : (![2, 1, 2] (2 : Fin 3) : ℝ) = 2 := by rfl
  rw [h0, h1, h2]
  norm_num

/-- Nontrivial heat-shear initial data have nonintegrable kinetic-energy
density on `ℝ^3`.  The proof uses the exact determinant-`4` Haar-scaling
identity coming from stretching only the `x₀` and `x₂` directions. -/
theorem not_integrable_heatShearKineticEnergyDensity
    {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
  intro hInt
  let x1 : NSSpace := EuclideanSpace.single nsCoord1 ((Real.pi / 2) / k)
  have hnonneg : ∀ x, 0 ≤ heatShearKineticEnergyDensity a k x := by
    intro x
    dsimp [heatShearKineticEnergyDensity]
    nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
  have hx1 : heatShearKineticEnergyDensity a k x1 ≠ 0 := by
    have hx1coord : x1 nsCoord1 = (Real.pi / 2) / k := by
      simp [x1, nsCoord1]
    have hkπ : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
      field_simp [hk]
    have hsin : Real.sin (k * x1 nsCoord1) = 1 := by
      rw [hx1coord, hkπ, Real.sin_pi_div_two]
    dsimp [heatShearKineticEnergyDensity]
    rw [hsin]
    simpa using (mul_ne_zero ha ha)
  have hpos : 0 < ∫ x, heatShearKineticEnergyDensity a k x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x1)
      (continuous_heatShearKineticEnergyDensity a k)
      hInt hnonneg hx1
  let I : ℝ := ∫ x, heatShearKineticEnergyDensity a k x
  have hcomp :
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x) = I := by
    calc
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x)
          = ∫ x, heatShearKineticEnergyDensity a k x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact congrArg (fun f : NSSpace → ℝ => f x)
                (heatShearKineticEnergyDensity_comp_heatShearLateralScaling a k)
      _ = I := by rfl
  have hdet : LinearMap.det heatShearLateralScaling ≠ 0 := by
    rw [det_heatShearLateralScaling]
    norm_num
  have hmap :
      MeasureTheory.Measure.map heatShearLateralScaling
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) =
        ENNReal.ofReal ((4 : ℝ)⁻¹) •
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)) (f := heatShearLateralScaling)
      hdet]
    simp [det_heatShearLateralScaling]
  have hchange :
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x) =
        ((4 : ℝ)⁻¹) * I := by
    calc
      ∫ x : NSSpace, heatShearKineticEnergyDensity a k (heatShearLateralScaling x)
          = ∫ y : NSSpace, heatShearKineticEnergyDensity a k y ∂
              MeasureTheory.Measure.map heatShearLateralScaling
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
              symm
              exact MeasureTheory.integral_map
                (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
                (heatShearLateralScaling.continuous_of_finiteDimensional.aemeasurable)
                ((continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable)
      _ = ((4 : ℝ)⁻¹) * I := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [I]
  have hEq : I = ((4 : ℝ)⁻¹) * I := by
    simpa [hcomp] using hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  linarith

/-- The initial kinetic-energy density of the heat-shear datum is the explicit
oscillatory density `(a * sin (k * x₁))²`. -/
theorem initialKineticEnergyDensity_heatShearInitialVelocity
    (a k : ℝ) :
    initialKineticEnergyDensity (heatShearInitialVelocity a k) =
      heatShearKineticEnergyDensity a k := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- On each time slice, the damped heat-shear field carries the same
oscillatory kinetic-energy density with the amplitude rescaled by the heat
factor `exp (-(ν * k²) * t)`. -/
theorem kineticEnergyDensity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearVelocityField ν a k) t =
      heatShearKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearVelocityField ν a k) t =
      initialKineticEnergyDensity (heatShearInitialVelocity A k) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearVelocityField_apply, heatShearInitialVelocity_apply]
    _ = heatShearKineticEnergyDensity A k :=
      initialKineticEnergyDensity_heatShearInitialVelocity A k
    _ = heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k := by
        simp [A]

/-- A nontrivial damped heat-shear field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density on any time slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (heatShearVelocityField ν a k) t) := by
  intro hInt
  have hA :
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≠ 0 := by
    exact mul_ne_zero ha (Real.exp_ne_zero _)
  have hIntHeat :
      MeasureTheory.Integrable
        (heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k) := by
    simpa [kineticEnergyDensity_heatShearVelocityField ν a k t] using hInt
  exact not_integrable_heatShearKineticEnergyDensity hA hk hIntHeat

/-- Therefore a nontrivial damped heat-shear field never satisfies the
concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ boundedKineticEnergy (heatShearVelocityField ν a k) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk 0 (hbound 0).1

/-- On every nonnegative slab, a nontrivial damped heat-shear field also fails
the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearVelocityField
    {ν a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVelocityField ν a k) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk 0 ((hbound 0 le_rfl hT).1)

/-- The initial kinetic-energy density of the heat-shear datum with added
constant vertical drift is the heat-shear density plus the constant drift term
`c²`. -/
theorem initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) :
    initialKineticEnergyDensity (heatShearVerticalDriftInitialVelocity a k c) =
      fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ) := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- On each time slice, the damped heat-shear field with additional constant
vertical drift carries the heat-shear energy density plus the constant drift
contribution `c²`. -/
theorem kineticEnergyDensity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t =
      fun x =>
        heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t =
      initialKineticEnergyDensity (heatShearVerticalDriftInitialVelocity A k c) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearVerticalDriftVelocityField_apply, heatShearVerticalDriftInitialVelocity_apply]
    _ = fun x => heatShearKineticEnergyDensity A k x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity A k c
    _ = fun x =>
        heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ) := by
        simp [A]

/-- A nontrivial damped heat-shear field with vertical drift is not spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearVerticalDriftVelocityField ν a k c) t) := by
  intro hInt
  have hA :
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≠ 0 := by
    exact mul_ne_zero ha (Real.exp_ne_zero _)
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x =>
          heatShearKineticEnergyDensity
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearVerticalDriftVelocityField ν a k c t] using hInt
  have hIntHeat :
      MeasureTheory.Integrable
        (heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx :
        0 ≤ heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg
        ((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity hA hk hIntHeat

/-- Therefore a nontrivial damped heat-shear field with vertical drift never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ boundedKineticEnergy (heatShearVerticalDriftVelocityField ν a k c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk 0 (hbound 0).1

/-- On every nonnegative slab, a nontrivial damped heat-shear field with
vertical drift also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
    {ν a k c T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVerticalDriftVelocityField ν a k c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the heat-shear initial datum at time `0` has the same
time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    kineticEnergyDensity u 0 = heatShearKineticEnergyDensity a k := by
  calc
    kineticEnergyDensity u 0 = initialKineticEnergyDensity (heatShearInitialVelocity a k) := by
      symm
      exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = heatShearKineticEnergyDensity a k :=
      initialKineticEnergyDensity_heatShearInitialVelocity a k

/-- Therefore any velocity field matching nontrivial heat-shear initial data
already fails the time-zero integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntHeat :
      MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    simpa [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearInitialVelocity hinit]
      using hInt
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- On every nonnegative slab, nontrivial heat-shear initial data rule out the
bounded-energy witness slot regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
      (u := u) ha hk hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching nontrivial heat-shear initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
    {u : NSVelocityField} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearInitialVelocity a k) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearInitialVelocity
      (u := u) ha hk hinit ((hbound 0).1)

/-- Nontrivial heat-shear initial data are not finite-energy admissible on
`ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearInitialVelocity
    {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity a k) := by
  intro hE
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearInitialVelocity a k] using hE
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a nontrivial heat-shear profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearInitialVelocity
    {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearInitialVelocity a k } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- Kinetic-energy density carried by the heat-shear initial profile with
constant streamwise drift
`x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftKineticEnergyDensity (a k d : ℝ) : NSSpace → ℝ :=
  fun x =>
    (d + a * Real.sin (k * x nsCoord1)) *
      (d + a * Real.sin (k * x nsCoord1))

/-- The heat-shear kinetic-energy density with constant streamwise drift is
continuous on `ℝ^3`. -/
theorem continuous_heatShearStreamwiseDriftKineticEnergyDensity
    (a k d : ℝ) :
    Continuous (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  have hsin : Continuous fun x : NSSpace => Real.sin (k * x nsCoord1) := by
    simpa [mul_assoc] using Real.continuous_sin.comp (continuous_const.mul hcoord)
  have hbase : Continuous fun x : NSSpace => d + a * Real.sin (k * x nsCoord1) := by
    exact continuous_const.add (continuous_const.mul hsin)
  exact hbase.mul hbase

/-- The heat-shear kinetic-energy density with streamwise drift is invariant
under the same lateral scaling that stretches only `x₀` and `x₂`. -/
theorem heatShearStreamwiseDriftKineticEnergyDensity_comp_heatShearLateralScaling
    (a k d : ℝ) :
    (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)) =
      heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  funext x
  simp [heatShearStreamwiseDriftKineticEnergyDensity, heatShearLateralScaling_apply_coord1]

/-- Any heat-shear profile with nonzero constant streamwise drift has
nonintegrable kinetic-energy density on `ℝ^3`.  The proof uses the same
determinant-`4` lateral scaling as pure heat shear, but now the witness point
is the origin where the density equals `d²`. -/
theorem not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
    {a k d : ℝ} (hd : d ≠ 0) :
    ¬ MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
  intro hInt
  let x0 : NSSpace := 0
  have hnonneg : ∀ x, 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
    intro x
    dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
    nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
  have hx0 : heatShearStreamwiseDriftKineticEnergyDensity a k d x0 ≠ 0 := by
    have hd2 : d * d ≠ 0 := mul_ne_zero hd hd
    simpa [x0, heatShearStreamwiseDriftKineticEnergyDensity] using hd2
  have hpos : 0 < ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x0)
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d)
      hInt hnonneg hx0
  let I : ℝ := ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x
  have hcomp :
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x) = I := by
    calc
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)
          = ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact congrArg (fun f : NSSpace → ℝ => f x)
                (heatShearStreamwiseDriftKineticEnergyDensity_comp_heatShearLateralScaling a k d)
      _ = I := by rfl
  have hdet : LinearMap.det heatShearLateralScaling ≠ 0 := by
    rw [det_heatShearLateralScaling]
    norm_num
  have hmap :
      MeasureTheory.Measure.map heatShearLateralScaling
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) =
        ENNReal.ofReal ((4 : ℝ)⁻¹) •
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)) (f := heatShearLateralScaling)
      hdet]
    simp [det_heatShearLateralScaling]
  have hchange :
      ∫ x, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x) =
        ((4 : ℝ)⁻¹) * I := by
    calc
      ∫ x : NSSpace, heatShearStreamwiseDriftKineticEnergyDensity a k d (heatShearLateralScaling x)
          = ∫ y : NSSpace, heatShearStreamwiseDriftKineticEnergyDensity a k d y ∂
              MeasureTheory.Measure.map heatShearLateralScaling
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
              symm
              exact MeasureTheory.integral_map
                (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
                (heatShearLateralScaling.continuous_of_finiteDimensional.aemeasurable)
                ((continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable)
      _ = ((4 : ℝ)⁻¹) * I := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [I]
  have hEq : I = ((4 : ℝ)⁻¹) * I := by
    simpa [hcomp] using hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  linarith

/-- The initial kinetic-energy density of the heat-shear datum with constant
streamwise drift is the explicit oscillatory density
`(d + a * sin (k * x₁))²`. -/
theorem initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) :
    initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity a k d) =
      heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  funext x
  rw [initialKineticEnergyDensity, heatShearStreamwiseDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the damped heat-shear field with constant streamwise
drift carries the same oscillatory density with the amplitude rescaled by the
heat factor `exp (-(ν * k²) * t)`. -/
theorem kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t =
      heatShearStreamwiseDriftKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t =
      initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity A k d) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearStreamwiseDriftVelocityField_apply, heatShearStreamwiseDriftInitialVelocity_apply]
    _ = heatShearStreamwiseDriftKineticEnergyDensity A k d :=
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity A k d
    _ = heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d := by
        simp [A]

/-- A heat-shear field with nonzero constant streamwise drift is never spatially
integrable on `ℝ^3` with respect to the kinetic-energy density on any time
slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
    {ν a k d : ℝ} (hd : d ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearStreamwiseDriftVelocityField ν a k d) t) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d) := by
    simpa [kineticEnergyDensity_heatShearStreamwiseDriftVelocityField ν a k d t] using hInt
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) (k := k) (d := d) hd hIntDrift

/-- Therefore a heat-shear field with nonzero constant streamwise drift never
satisfies the concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
    {ν a k d : ℝ} (hd : d ≠ 0) :
    ¬ boundedKineticEnergy (heatShearStreamwiseDriftVelocityField ν a k d) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd 0 (hbound 0).1

/-- On every nonnegative slab, a heat-shear field with nonzero constant
streamwise drift also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
    {ν a k d T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearStreamwiseDriftVelocityField ν a k d) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the heat-shear initial datum with nonzero constant
streamwise drift at time `0` has the same time-zero kinetic-energy density as
that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    kineticEnergyDensity u 0 = heatShearStreamwiseDriftKineticEnergyDensity a k d := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearStreamwiseDriftInitialVelocity a k d) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = heatShearStreamwiseDriftKineticEnergyDensity a k d :=
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity a k d

/-- Therefore any velocity field matching heat-shear initial data with nonzero
constant streamwise drift already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        hinit] using hInt
  exact not_integrable_heatShearStreamwiseDriftKineticEnergyDensity (a := a) (k := k) hd hIntDrift

/-- On every nonnegative slab, heat-shear initial data with nonzero constant
streamwise drift rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
      (u := u) hd hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching heat-shear initial data with nonzero constant streamwise drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
    {u : NSVelocityField} {a k d : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
      (u := u) hd hinit ((hbound 0).1)

/-- Heat-shear initial data with nonzero constant streamwise drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity
    {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearStreamwiseDriftInitialVelocity a k d] using hE
  exact not_integrable_heatShearStreamwiseDriftKineticEnergyDensity (a := a) (k := k) hd hIntDrift

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a heat-shear profile with nonzero constant
streamwise drift. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearStreamwiseDriftInitialVelocity
    {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearStreamwiseDriftInitialVelocity a k d } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- If a velocity field matches the initial data
`x ↦ (a * sin (k * x₁), 0, c)` at time `0`, then its time-zero kinetic-energy
density is the heat-shear density plus the constant vertical drift
contribution `c²`. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ) := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [kineticEnergyDensity, hinit x, heatShearVerticalDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, hs]

/-- Therefore any velocity field matching nontrivial heat-shear initial data
with vertical drift already fails the time-zero integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        hinit] using hInt
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- On every nonnegative slab, nontrivial heat-shear initial data with vertical
drift rule out the bounded-energy witness slot regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
      (u := u) ha hk hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching nontrivial heat-shear initial data with vertical drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
      (u := u) ha hk hinit ((hbound 0).1)

/-- Nontrivial heat-shear initial data with vertical drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity
    {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearKineticEnergyDensity a k x + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearVerticalDriftInitialVelocity a k c] using hE
  have hIntHeat : MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact not_integrable_heatShearKineticEnergyDensity ha hk hIntHeat

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a nontrivial heat-shear profile with vertical drift.
-/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearVerticalDriftInitialVelocity
    {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearVerticalDriftInitialVelocity a k c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The initial kinetic-energy density of the heat-shear datum with full
constant drift is the streamwise-drift density plus the constant vertical drift
term `c²`. -/
theorem initialKineticEnergyDensity_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) :
    initialKineticEnergyDensity (heatShearFullDriftInitialVelocity a k d c) =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) := by
  funext x
  rw [initialKineticEnergyDensity, heatShearFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the damped heat-shear field with full constant drift
carries the streamwise-drift density plus the constant vertical drift
contribution `c²`. -/
theorem kineticEnergyDensity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t =
      fun x =>
        heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d x + c ^ (2 : ℕ) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t =
      initialKineticEnergyDensity (heatShearFullDriftInitialVelocity A k d c) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearFullDriftVelocityField_apply, heatShearFullDriftInitialVelocity_apply]
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity A k d x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity A k d c
    _ = fun x =>
        heatShearStreamwiseDriftKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k d x + c ^ (2 : ℕ) := by
        simp [A]

/-- A heat-shear field with nonzero constant streamwise drift remains
nonintegrable on `ℝ^3` even after adding an arbitrary constant vertical drift. -/
theorem not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
    {ν a k d c : ℝ} (hd : d ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearFullDriftVelocityField ν a k d c) t) := by
  intro hInt
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity A k d x + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearFullDriftVelocityField ν a k d c t, A] using hInt
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity A k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity A k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity A k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + A * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := A) (k := k) (d := d) hd hIntStreamwise

/-- Therefore a heat-shear field with nonzero streamwise drift still fails the
global bounded-energy predicate after any added constant vertical drift. -/
theorem not_boundedKineticEnergy_heatShearFullDriftVelocityField
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    ¬ boundedKineticEnergy (heatShearFullDriftVelocityField ν a k d c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd 0 (hbound 0).1

/-- On every nonnegative slab, the full-drift heat-shear family also fails the
finite-time bounded-energy predicate whenever the streamwise drift is nonzero.
-/
theorem not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
    {ν a k d c T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearFullDriftVelocityField ν a k d c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the full-drift heat-shear datum at time `0` has the
same time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearFullDriftInitialVelocity a k d c) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity a k d c

/-- Therefore any velocity field matching full-drift heat-shear initial data
with nonzero streamwise drift already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        hinit] using hInt
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a) (k := k) (d := d) hd hIntStreamwise

/-- On every nonnegative slab, full-drift heat-shear initial data with nonzero
streamwise drift rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c T : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
      (u := u) hd hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching full-drift heat-shear initial data with nonzero streamwise drift. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
    {u : NSVelocityField} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
      (u := u) hd hinit ((hbound 0).1)

/-- Full-drift heat-shear initial data with nonzero streamwise drift are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
    {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) := by
  intro hE
  have hIntDrift :
      MeasureTheory.Integrable
        (fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearFullDriftInitialVelocity a k d c] using hE
  have hIntStreamwise :
      MeasureTheory.Integrable (heatShearStreamwiseDriftKineticEnergyDensity a k d) := by
    refine MeasureTheory.Integrable.mono' hIntDrift
      (continuous_heatShearStreamwiseDriftKineticEnergyDensity a k d).aestronglyMeasurable ?_
    filter_upwards with x
    have hx : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    rw [Real.norm_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  exact
    not_integrable_heatShearStreamwiseDriftKineticEnergyDensity
      (a := a) (k := k) (d := d) hd hIntStreamwise

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a full-drift heat-shear profile with nonzero
streamwise drift. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDriftInitialVelocity
    {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearFullDriftInitialVelocity a k d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The initial kinetic-energy density of the transported heat-shear datum is
the heat-shear density plus the constant transport-speed contribution `b²`. -/
theorem initialKineticEnergyDensity_heatShearTransportInitialVelocity
    (a k b : ℝ) :
    initialKineticEnergyDensity (heatShearTransportInitialVelocity a k b) =
      fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
  funext x
  have hs :
      |a| * |Real.sin (k * x.ofLp 1)| * (|a| * |Real.sin (k * x.ofLp 1)|) =
        a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
    simpa [pow_two, abs_mul, mul_assoc, mul_left_comm, mul_comm] using
      (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearTransportInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, heatShearKineticEnergyDensity, pow_two]
  simpa using congrArg (fun r : ℝ => r + b ^ (2 : ℕ)) hs

/-- On each time slice, the transported heat-shear field carries the transported
oscillatory energy density plus the constant transport-speed contribution
`b²`. -/
theorem kineticEnergyDensity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearTransportVelocityField ν a k b) t =
      fun x =>
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) +
        b ^ (2 : ℕ) := by
  funext x
  have hexp :
      0 ≤ Real.exp (-(ν * k ^ (2 : ℕ)) * t) := by
    exact le_of_lt (Real.exp_pos _)
  have hs :
      |a| *
          (Real.exp (-(ν * (k * (k * t)))) *
            (|Real.sin (k * (x.ofLp 1 - b * t))| *
              (|a| *
                (Real.exp (-(ν * (k * (k * t)))) *
                  |Real.sin (k * (x.ofLp 1 - b * t))|)))) =
        a *
          (Real.exp (-(ν * (k * (k * t)))) *
            (Real.sin (k * (x.ofLp 1 - b * t)) *
              (a *
                (Real.exp (-(ν * (k * (k * t)))) *
                  Real.sin (k * (x.ofLp 1 - b * t)))))) := by
    simpa [pow_two, abs_mul, abs_of_nonneg hexp, mul_assoc, mul_left_comm, mul_comm] using
      (sq_abs (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        Real.sin (k * (x.ofLp 1 - b * t))))
  rw [kineticEnergyDensity, heatShearTransportVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, pow_two, mul_assoc]
  simpa using congrArg (fun r : ℝ => r + b ^ (2 : ℕ)) hs

/-- A transported heat-shear field with nonzero transport speed has
nonintegrable kinetic-energy density on every time slice because it dominates
the nonzero constant field `(0, b, 0)`. -/
theorem not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
    {ν a k b : ℝ} (hb : b ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearTransportVelocityField ν a k b) t) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace =>
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearTransportVelocityField ν a k b t] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hsq :
        0 ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) := by
      nlinarith [sq_nonneg
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.sin (k * (x nsCoord1 - b * t)))]
    have hsum :
        0 ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- Therefore a transported heat-shear field with nonzero transport speed never
satisfies the global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearTransportVelocityField
    {ν a k b : ℝ} (hb : b ≠ 0) :
    ¬ boundedKineticEnergy (heatShearTransportVelocityField ν a k b) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb 0 (hbound 0).1

/-- On every nonnegative slab, a transported heat-shear field with nonzero
transport speed also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
    {ν a k b T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportVelocityField ν a k b) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the transported heat-shear datum at time `0` has the
same time-zero kinetic-energy density as that explicit initial profile. -/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearTransportInitialVelocity a k b) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearTransportInitialVelocity a k b

/-- Therefore any velocity field matching transported heat-shear initial data
with nonzero transport speed already fails the time-zero integrability
requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        hinit] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    have hsum : 0 ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      nlinarith
    have hbound : ‖b ^ (2 : ℕ)‖ ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- On every nonnegative slab, transported heat-shear initial data with nonzero
transport speed rule out the bounded-energy witness slot regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
      (u := u) hb hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching transported heat-shear initial data with nonzero transport speed. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
    {u : NSVelocityField} {a k b : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportInitialVelocity
      (u := u) hb hinit ((hbound 0).1)

/-- Transported heat-shear initial data with nonzero transport speed are not
finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity
    {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) := by
  intro hE
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearTransportInitialVelocity a k b] using hE
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearKineticEnergyDensity a k x := by
      dsimp [heatShearKineticEnergyDensity]
      nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
    have hsum : 0 ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      nlinarith
    have hbound : ‖b ^ (2 : ℕ)‖ ≤ heatShearKineticEnergyDensity a k x + b ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a transported heat-shear profile with nonzero
transport speed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportInitialVelocity
    {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportInitialVelocity a k b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The initial kinetic-energy density of the transported full-drift
heat-shear datum is the full-drift heat-shear density plus the constant
transport-speed contribution `b²`. -/
theorem initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) :
    initialKineticEnergyDensity (heatShearTransportFullDriftInitialVelocity a k b d c) =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  rw [initialKineticEnergyDensity, heatShearTransportFullDriftInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, heatShearStreamwiseDriftKineticEnergyDensity, pow_two]

/-- On each time slice, the transported full-drift heat-shear field carries
the transported full-drift oscillatory density together with the constant
transport and vertical drift contributions `b² + c²`. -/
theorem kineticEnergyDensity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearTransportFullDriftVelocityField ν a k b d c) t =
      fun x =>
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) *
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            Real.sin (k * (x nsCoord1 - b * t))) +
        b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  funext x
  rw [kineticEnergyDensity, heatShearTransportFullDriftVelocityField_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, nsCoord2, pow_two, mul_assoc]

/-- A transported full-drift heat-shear field with nonzero transport speed has
nonintegrable kinetic-energy density on every time slice because it still
dominates the nonzero constant field `(0, b, 0)`. -/
theorem not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
    {ν a k b d c : ℝ} (hb : b ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (heatShearTransportFullDriftVelocityField ν a k b d c) t) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace =>
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [kineticEnergyDensity_heatShearTransportFullDriftVelocityField ν a k b d c t] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hsq :
        0 ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) := by
      nlinarith [sq_nonneg
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.sin (k * (x nsCoord1 - b * t)))]
    have hsum :
        0 ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) *
            (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) +
          b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- Therefore a transported full-drift heat-shear field with nonzero transport
speed never satisfies the global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    ¬ boundedKineticEnergy (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb 0 (hbound 0).1

/-- On every nonnegative slab, a transported full-drift heat-shear field with
nonzero transport speed also fails the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
    {ν a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb 0 ((hbound 0 le_rfl hT).1)

/-- Any field matching the transported full-drift heat-shear datum at time `0`
has the same time-zero kinetic-energy density as that explicit initial profile.
-/
theorem kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    kineticEnergyDensity u 0 =
      fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
  calc
    kineticEnergyDensity u 0 =
        initialKineticEnergyDensity (heatShearTransportFullDriftInitialVelocity a k b d c) := by
          symm
          exact initialKineticEnergyDensity_eq_of_matchesInitialVelocity hinit
    _ = fun x => heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) :=
      initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity a k b d c

/-- Therefore any velocity field matching transported full-drift heat-shear
initial data with nonzero transport speed already fails the time-zero
integrability requirement. -/
theorem not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity u 0) := by
  intro hInt
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearStreamwiseDriftKineticEnergyDensity a k d x +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa
      [kineticEnergyDensity_zero_eq_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        hinit] using hInt
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    have hsum :
        0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) +
          c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- On every nonnegative slab, transported full-drift heat-shear initial data
with nonzero transport speed rule out the bounded-energy witness slot
regardless of later dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
      (u := u) hb hinit ((hbound 0 le_rfl hT).1)

/-- The same obstruction rules out global bounded kinetic energy for any field
matching transported full-drift heat-shear initial data with nonzero
transport speed. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
    {u : NSVelocityField} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hinit : MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
      (u := u) hb hinit ((hbound 0).1)

/-- Transported full-drift heat-shear initial data with nonzero transport
speed are not finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity
    {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hE
  have hIntTransport :
      MeasureTheory.Integrable
        (fun x : NSSpace => heatShearStreamwiseDriftKineticEnergyDensity a k d x +
          b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
    simpa [finiteInitialKineticEnergy,
      initialKineticEnergyDensity_heatShearTransportFullDriftInitialVelocity a k b d c] using hE
  have hIntConst : MeasureTheory.Integrable (fun _ : NSSpace => b ^ (2 : ℕ)) := by
    refine MeasureTheory.Integrable.mono' hIntTransport
      (continuous_const.aestronglyMeasurable) ?_
    filter_upwards with x
    have hheat : 0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x := by
      dsimp [heatShearStreamwiseDriftKineticEnergyDensity]
      nlinarith [sq_nonneg (d + a * Real.sin (k * x nsCoord1))]
    have hsum :
        0 ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      nlinarith
    have hbound :
        ‖b ^ (2 : ℕ)‖ ≤ heatShearStreamwiseDriftKineticEnergyDensity a k d x + b ^ (2 : ℕ) +
          c ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    exact hbound
  have hconstNe : EuclideanSpace.single nsCoord1 b ≠ (0 : NSSpace) := by
    simpa using hb
  have hIntConstField :
      MeasureTheory.Integrable
        (kineticEnergyDensity (constantVelocityField (EuclideanSpace.single nsCoord1 b)) 0) := by
    simpa [kineticEnergyDensity_constantVelocityField, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_three, nsCoord0, nsCoord1, nsCoord2, pow_two] using hIntConst
  exact
    not_integrable_kineticEnergyDensity_constantVelocityField
      (c := EuclideanSpace.single nsCoord1 b) hconstNe 0 hIntConstField

/-- The repaired structured whole-space input domain contains no problem datum
whose initial velocity is a transported full-drift heat-shear profile with
nonzero transport speed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDriftInitialVelocity
    {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportFullDriftInitialVelocity a k b d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- Therefore the repaired structured whole-space input domain contains no
problem datum whose initial velocity is a nonzero linear shear field. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearInitialVelocity
    {a : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearInitialVelocity a } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, 0, b)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearVerticalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearVerticalDriftInitialVelocity a b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, b, 0)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearHorizontalDriftInitialVelocity
    {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearHorizontalDriftInitialVelocity a b } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The same repaired structured whole-space input domain contains no problem
datum whose initial velocity is the nonzero affine shear profile
`x ↦ (a * x₁, b, c)`. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity
    {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearFullDriftInitialVelocity a b c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- Hence any nonnegative finite-time slab witness with nonzero linear shear
initial data is blocked by the bounded-energy slot, regardless of later
dynamics. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
      ha hinit ((hbound 0 le_rfl hT).1)

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, 0, b)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      ha hinit ((hbound 0 le_rfl hT).1)

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      ha hinit ((hbound 0 le_rfl hT).1)

/-- The same time-zero obstruction blocks any nonnegative finite-time slab
witness matching the initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ} {T : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ boundedKineticEnergyUpTo u T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      ha hinit ((hbound 0 le_rfl hT).1)

/-- The steady linear shear field is an exact smooth incompressible NS
candidate on every nonnegative slab with a uniform vorticity bound; the only
missing finite-time witness slot is bounded kinetic energy. -/
theorem linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨linearShearVelocityField a, 0, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVelocityField a
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simp [timeVelocityDerivative_linearShearVelocityField,
      spatialConvection_linearShearVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVelocityField]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearVelocityField a t x
  · exact matchesInitialVelocity_linearShearVelocityField a
  · exact uniformVorticityBoundUpTo_linearShearVelocityField a T
  · exact not_boundedKineticEnergyUpTo_linearShearVelocityField
      (a := a) ha hT

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy. -/
theorem linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨linearShearVerticalDriftVelocityField a b, 0, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField a b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simp [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
      spatialConvection_linearShearVerticalDriftVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVerticalDriftVelocityField]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearVerticalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearVerticalDriftVelocityField a b
  · exact uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField a b T
  · exact not_boundedKineticEnergyUpTo_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha hT

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy.  Here the nonzero convection is cancelled by the
explicit affine pressure field. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine
    ⟨linearShearHorizontalDriftVelocityField a b,
      linearShearHorizontalDriftPressureField a b, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x ht0 htT
    rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      spatialConvection_linearShearHorizontalDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearHorizontalDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearHorizontalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearHorizontalDriftVelocityField a b
  · exact uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField a b T
  · exact not_boundedKineticEnergyUpTo_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha hT

/-- The same affine-shear slab candidate remains valid after adding any smooth
slice-wise zero-spatial-gradient pressure gauge.  The bounded-energy slot on
`ℝ^3` is still the only missing witness component. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (a := a) (b := b) ha hT)
      q hq hq_zero

/-- Time-only special case of the horizontal affine-shear pressure-gauge
transport on the uniform-vorticity candidate surface. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The steady field `u(t,x) = (a * x₁, b, c)` is also an exact smooth
incompressible NS candidate on every nonnegative slab with the same uniform
vorticity bound `|a|`; the only missing finite-time witness slot is again
bounded kinetic energy.  The vertical drift does not change the same affine
pressure cancellation already needed for the horizontal branch. -/
theorem linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine
    ⟨linearShearFullDriftVelocityField a b c,
      linearShearHorizontalDriftPressureField a b, |a|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearFullDriftVelocityField a b c
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x ht0 htT
    rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
      spatialConvection_linearShearFullDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearFullDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x ht0 htT
    exact spatialDivergence_linearShearFullDriftVelocityField a b c t x
  · exact matchesInitialVelocity_linearShearFullDriftVelocityField a b c
  · exact uniformVorticityBoundUpTo_linearShearFullDriftVelocityField a b c T
  · exact not_boundedKineticEnergyUpTo_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha hT

/-- The same obstruction rules out the global bounded-energy predicate for any
velocity field with nonzero linear shear initial data. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
    {u : NSVelocityField} {a : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearInitialVelocity a) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearInitialVelocity
      ha hinit ((hbound 0).1)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, 0, b)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      ha hinit ((hbound 0).1)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, b, 0)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
    {u : NSVelocityField} {a b : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      ha hinit ((hbound 0).1)

/-- The same global bounded-energy obstruction holds for the affine shear
datum `x ↦ (a * x₁, b, c)`. -/
theorem not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
    {u : NSVelocityField} {a b c : ℝ}
    (ha : a ≠ 0)
    (hinit : MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u) :
    ¬ boundedKineticEnergy u := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_zero_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      ha hinit ((hbound 0).1)

/-- The steady linear shear field is already a full exact candidate on the
global explicit theorem surface; the only missing slot is bounded kinetic
energy. -/
theorem linearShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨linearShearVelocityField a, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVelocityField a
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simp [timeVelocityDerivative_linearShearVelocityField,
      spatialConvection_linearShearVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVelocityField]
  · intro t x
    exact spatialDivergence_linearShearVelocityField a t x
  · exact matchesInitialVelocity_linearShearVelocityField a
  · exact not_boundedKineticEnergy_linearShearVelocityField
      (a := a) ha

/-- Linear shear therefore exhibits the exact mismatch on the global explicit
theorem surface: an honest smooth PDE-side candidate exists, but the explicit
global-output proposition is still false because bounded kinetic energy fails. -/
theorem linearShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, 0, b)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot. -/
theorem linearShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨linearShearVerticalDriftVelocityField a b, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField a b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simp [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
      spatialConvection_linearShearVerticalDriftVelocityField,
      spatialPressureGradient_zero,
      spatialLaplacian_linearShearVerticalDriftVelocityField]
  · intro t x
    exact spatialDivergence_linearShearVerticalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearVerticalDriftVelocityField a b
  · exact not_boundedKineticEnergy_linearShearVerticalDriftVelocityField
      (a := a) (b := b) ha

/-- Affine shear therefore exhibits the same exact mismatch on the global
explicit theorem surface: an honest smooth PDE-side candidate exists, but the
explicit global-output proposition is still false because bounded kinetic
energy fails. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, b, 0)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot.  The pressure field is now essential rather
than zero. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u := by
  refine
    ⟨linearShearHorizontalDriftVelocityField a b,
      linearShearHorizontalDriftPressureField a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x
    rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      spatialConvection_linearShearHorizontalDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearHorizontalDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x
    exact spatialDivergence_linearShearHorizontalDriftVelocityField a b t x
  · exact matchesInitialVelocity_linearShearHorizontalDriftVelocityField a b
  · exact not_boundedKineticEnergy_linearShearHorizontalDriftVelocityField
      (a := a) (b := b) ha

/-- Affine shear with horizontal drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
        (u := u) ha hinit hbd

/-- The steady affine shear field `u(t,x) = (a * x₁, b, c)` is likewise a full
exact candidate on the global explicit theorem surface; bounded kinetic energy
is again the only missing slot, and the same affine pressure already balances
the nonzero convection. -/
theorem linearShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a b c : ℝ} (ha : a ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      ¬ boundedKineticEnergy u := by
  refine
    ⟨linearShearFullDriftVelocityField a b c,
      linearShearHorizontalDriftPressureField a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_linearShearFullDriftVelocityField a b c
  · exact smoothSpaceTimePressure_linearShearHorizontalDriftPressureField a b
  · intro t x
    rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
      spatialConvection_linearShearFullDriftVelocityField,
      spatialPressureGradient_linearShearHorizontalDriftPressureField,
      spatialLaplacian_linearShearFullDriftVelocityField]
    ext i
    fin_cases i <;> simp [nsCoord0]
  · intro t x
    exact spatialDivergence_linearShearFullDriftVelocityField a b c t x
  · exact matchesInitialVelocity_linearShearFullDriftVelocityField a b c
  · exact not_boundedKineticEnergy_linearShearFullDriftVelocityField
      (a := a) (b := b) (c := c) ha

/-- Affine shear with full constant drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem linearShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a b c : ℝ} (ha : a ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (b := b) (c := c) ha
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
        (u := u) ha hinit hbd

/-- The damped sinusoidal heat-shear field is likewise an honest exact
candidate on the global explicit theorem surface; the only missing slot is
bounded kinetic energy on `ℝ^3`. -/
theorem heatShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearVelocityField ν a k, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVelocityField ν a k
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearVelocityField_zeroPressure ν a k t x
  · intro t x
    simpa using spatialDivergence_heatShearVelocityField ν a k t x
  · exact matchesInitialVelocity_heatShearVelocityField ν a k
  · exact not_boundedKineticEnergy_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk

/-- The damped sinusoidal heat-shear field therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) ha hk
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
        (u := u) ha hk hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
nontrivial heat-shear initial data, independent of any later pressure field. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (heatShearInitialVelocity a k) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearInitialVelocity
      (u := u) ha hk hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for nontrivial heat-shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearInitialVelocity a k) :=
    smoothInitialVelocityData_heatShearInitialVelocity a k
  have hdiv : ∀ x, initialSpatialDivergence (heatShearInitialVelocity a k) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearInitialVelocity a k x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity ha hk
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- Therefore the explicit finite-time witness type is uninhabited on any
nonnegative slab for nonzero linear shear initial data. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, 0, b)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, b, 0)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- The same witness-level obstruction applies to the affine shear datum
`x ↦ (a * x₁, b, c)` on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  intro hW
  rcases hW with ⟨W⟩
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      (u := W.velocity) ha hT W.initial_condition W.bounded_energy_on

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
is an exact smooth incompressible candidate with explicit slab vorticity bound
`|a * k|`; bounded kinetic energy is the only missing witness slot. -/
theorem heatShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearVelocityField ν a k, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVelocityField ν a k
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearVelocityField_zeroPressure ν a k t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearVelocityField ν a k t x
  · exact matchesInitialVelocity_heatShearVelocityField ν a k
  · exact uniformVorticityBoundUpTo_heatShearVelocityField ν a k T hν
  · exact not_boundedKineticEnergyUpTo_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk hT

/-- The same witness-level obstruction applies to the nontrivial heat-shear
datum on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)
      hT

/-- Heat shear exposes the same exact gap on the explicit uniform-vorticity
surface: there is an exact smooth incompressible candidate with a uniform slab
vorticity bound, but the finite-time witness type is still empty because
bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT

/-- Linear shear exposes the exact gap on the explicit uniform-vorticity
surface: there is an exact smooth incompressible candidate with a uniform slab
vorticity bound, but the concrete finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, 0, b)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, b, 0)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same horizontal affine-shear gap persists after adding any smooth
slice-wise zero-spatial-gradient pressure gauge to the explicit slab
candidate. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact
      linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- Time-only special case of the horizontal affine-shear pressure-gauge gap on
the explicit uniform-vorticity continuation surface. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The same explicit uniform-vorticity gap persists for the affine shear datum
`x ↦ (a * x₁, b, c)`: an exact smooth incompressible candidate with uniform slab
vorticity bound exists, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT

/-- The fully explicit global-output surface is likewise impossible for nonzero
linear shear initial data, independent of what pressure field is used later. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, 0, b)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearVerticalDriftInitialVelocity a b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearFullDriftInitialVelocity a b c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      (u := u) ha hinit hbd

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero linear shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearInitialVelocity a) :=
    smoothInitialVelocityData_linearShearInitialVelocity a
  have hdiv : ∀ x, initialSpatialDivergence (linearShearInitialVelocity a) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity a x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearVerticalDriftInitialVelocity a b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearVerticalDriftInitialVelocity a b) :=
    smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
  have hdiv : ∀ x, initialSpatialDivergence (linearShearVerticalDriftInitialVelocity a b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearHorizontalDriftInitialVelocity a b) :=
    smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
  have hdiv : ∀ x, initialSpatialDivergence (linearShearHorizontalDriftInitialVelocity a b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data `x ↦ (a * x₁, b, c)` on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearFullDriftInitialVelocity a b c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearFullDriftInitialVelocity a b c) :=
    smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
  have hdiv : ∀ x, initialSpatialDivergence (linearShearFullDriftInitialVelocity a b c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The repaired explicit regularity clause is vacuous on nonzero linear shear
data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearInitialVelocity a) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired explicit regularity clause can therefore be true on nonzero
linear shear initial data while the unrepaired concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity_without_regularity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearInitialVelocity a) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity
      (ν := ν) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data because the repaired finite-energy hypothesis already fails.
-/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearVerticalDriftInitialVelocity a b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data `x ↦ (a * x₁, b, 0)` because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearHorizontalDriftInitialVelocity a b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data `x ↦ (a * x₁, b, c)` because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearFullDriftInitialVelocity a b c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data while the unrepaired concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        (ν := ν) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data `x ↦ (a * x₁, b, c)` while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        (ν := ν) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The repaired explicit regularity clause is likewise vacuous on nontrivial
heat-shear data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearInitialVelocity a k) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired explicit regularity clause can therefore also be true on
nontrivial heat-shear initial data while the unrepaired concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity_without_regularity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearInitialVelocity a k) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity
      (ν := ν) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The structured fully concrete clause also rejects nonzero linear shear
initial data.  Again this is the explicit obstruction transported through the
concrete equivalence theorem. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity a
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity a
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity a x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearInitialVelocity a)
        hν
      (smoothInitialVelocityData_linearShearInitialVelocity a)
      (by
          intro x
          simpa using initialSpatialDivergence_linearShearInitialVelocity a x)).mp hClause)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearVerticalDriftInitialVelocity a b)
        hν
        (smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x)).mp hClause)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearHorizontalDriftInitialVelocity a b)
        hν
        (smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x)).mp hClause)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity a b c
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearFullDriftInitialVelocity a b c)
        hν
        (smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x)).mp hClause)

/-- The structured fully concrete clause also rejects nontrivial heat-shear
initial data. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity a k
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity a k
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity a k x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity ha hk
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearInitialVelocity a k)
        hν
        (smoothInitialVelocityData_heatShearInitialVelocity a k)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearInitialVelocity a k x)).mp hClause)

/-- The current fully explicit concrete local surrogate millennium target is
already false: nonzero linear shear initial data are admitted as smooth
divergence-free input, but cannot satisfy the bounded-energy output slot.  This
refutes the over-broad local `ℝ^3` surrogate only; it is kept as a regression
guard against reintroducing that theorem-shape bug, not as a refutation of
narrower manuscript-compatible input surfaces. -/
theorem not_ExplicitConcreteNavierStokesMillenniumTarget :
    ¬ ExplicitConcreteNavierStokesMillenniumTarget := by
  intro hTarget
  have hν : 0 < (1 : ℝ) := by positivity
  exact
    not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity
      (ν := 1) (a := 1) hν one_ne_zero
      (hTarget 1 (linearShearInitialVelocity 1))

/-- Hence the structured fully concrete theorem target is also false.  The bug
is in the chosen admissible-data surface, not in the equivalence theorem. -/
theorem not_ConcreteNavierStokesMillenniumTarget :
    ¬ ConcreteNavierStokesMillenniumTarget := by
  intro hTarget
  exact
    not_ExplicitConcreteNavierStokesMillenniumTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        hTarget)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero linear shear initial data because the
quantified finite-time witness type is already uninhabited there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearInitialVelocity a)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
        (ν := ν) (T := T) ha hT)

/-- The uniform continuation clause can therefore be true on nonzero linear
shear initial data even though the concrete regularity clause is false there.
-/
theorem ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero linear shear data, now for the stronger reason that the finite-energy
input hypothesis itself already fails.  No horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero linear shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data because the
finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data
`x ↦ (a * x₁, b, 0)` because the finite-time witness type is already empty
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also trivially satisfied for nonzero affine shear initial data
`x ↦ (a * x₁, b, c)` because the finite-time witness type is already empty
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT)

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data even though the concrete regularity clause is false
there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data `x ↦ (a * x₁, b, 0)` even though the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The uniform continuation clause can therefore also be true on nonzero
affine shear initial data `x ↦ (a * x₁, b, c)` even though the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data because the finite-energy input hypothesis already
fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data `x ↦ (a * x₁, b, 0)` because the finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero affine shear data `x ↦ (a * x₁, b, c)` because the finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired uniform-vorticity clause can therefore also be true on
nonzero affine shear data `x ↦ (a * x₁, b, c)` while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for nontrivial heat-shear initial data because the finite-time
witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearInitialVelocity a k)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) ha hk hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nontrivial heat-shear data because the repaired finite-energy hypothesis
already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired uniform-vorticity clause can therefore also be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The damped sinusoidal heat-shear field with constant streamwise drift is
likewise an honest exact candidate on the global explicit theorem surface; the
only missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k d : ℝ} (hd : d ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearStreamwiseDriftVelocityField ν a k d, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure ν a k d t x
  · intro t x
    simpa using spatialDivergence_heatShearStreamwiseDriftVelocityField ν a k d t x
  · exact matchesInitialVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · exact not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd

/-- Heat shear with constant streamwise drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k d : ℝ} (hd : d ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (d := d) hd
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
        (u := u) hd hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
heat-shear initial data with nonzero constant streamwise drift. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearStreamwiseDriftInitialVelocity
      (u := u) hd hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for heat-shear initial data with nonzero constant streamwise
drift on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearStreamwiseDriftInitialVelocity a k d) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearStreamwiseDriftInitialVelocity a k d) :=
    smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
  have hdiv : ∀ x, initialSpatialDivergence (heatShearStreamwiseDriftInitialVelocity a k d) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity hd
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to the heat-shear datum with
nonzero constant streamwise drift on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
with constant streamwise drift is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearStreamwiseDriftVelocityField ν a k d, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure ν a k d t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearStreamwiseDriftVelocityField ν a k d t x
  · exact matchesInitialVelocity_heatShearStreamwiseDriftVelocityField ν a k d
  · exact uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField ν a k d T hν
  · exact not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) hd hT

/-- Heat shear with constant streamwise drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT

/-- The repaired explicit regularity clause is likewise vacuous on heat-shear
data with nonzero constant streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired explicit regularity clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The structured fully concrete clause also rejects heat-shear initial data
with nonzero constant streamwise drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity
    {ν : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity a k d
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity hd
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
        hν
        (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x)).mp hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for heat-shear initial data with nonzero constant streamwise drift
because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The repaired uniform-vorticity continuation clause is also vacuous on
heat-shear data with nonzero constant streamwise drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired uniform-vorticity clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The damped sinusoidal heat-shear field with constant vertical drift is
likewise an honest exact candidate on the global explicit theorem surface; the
only missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearVerticalDriftVelocityField ν a k c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField ν a k c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure ν a k c t x
  · intro t x
    simpa using spatialDivergence_heatShearVerticalDriftVelocityField ν a k c t x
  · exact matchesInitialVelocity_heatShearVerticalDriftVelocityField ν a k c
  · exact not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk

/-- Heat shear with constant vertical drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k c : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (c := c) ha hk
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
        (u := u) ha hk hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
nontrivial heat-shear initial data with vertical drift. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearVerticalDriftInitialVelocity
      (u := u) ha hk hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for nontrivial heat-shear initial data with vertical drift on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearVerticalDriftInitialVelocity a k c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearVerticalDriftInitialVelocity a k c) :=
    smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearVerticalDriftInitialVelocity a k c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity ha hk
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to the nontrivial heat-shear
datum with vertical drift on every nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the heat-shear field
with constant vertical drift is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T -> spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearVerticalDriftVelocityField ν a k c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField ν a k c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure ν a k c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearVerticalDriftVelocityField ν a k c t x
  · exact matchesInitialVelocity_heatShearVerticalDriftVelocityField ν a k c
  · exact uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField ν a k c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
      (ν := ν) (a := a) (k := k) (c := c) ha hk hT

/-- Heat shear with constant vertical drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT

/-- The repaired explicit regularity clause is likewise vacuous on nontrivial
heat-shear data with vertical drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearVerticalDriftInitialVelocity a k c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired explicit regularity clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the unrepaired concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The structured fully concrete clause also rejects nontrivial heat-shear
initial data with vertical drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity
    {ν : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity a k c
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity ha hk
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearVerticalDriftInitialVelocity a k c)
        hν
        (smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x)).mp hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for nontrivial heat-shear initial data with vertical drift
because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nontrivial heat-shear data with vertical drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired uniform-vorticity clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The damped sinusoidal heat-shear field with full constant drift is likewise
an honest exact candidate on the global explicit theorem surface; the only
missing slot is bounded kinetic energy on `ℝ^3`. -/
theorem heatShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearFullDriftVelocityField ν a k d c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearFullDriftVelocityField ν a k d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure ν a k d c t x
  · intro t x
    simpa using spatialDivergence_heatShearFullDriftVelocityField ν a k d c t x
  · exact matchesInitialVelocity_heatShearFullDriftVelocityField ν a k d c
  · exact not_boundedKineticEnergy_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd

/-- Heat shear with full constant drift therefore exhibits the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k d c : ℝ} (hd : d ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
        (u := u) hd hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
heat-shear initial data with full constant drift whenever the streamwise drift
is nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearFullDriftInitialVelocity a k d c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearFullDriftInitialVelocity
      (u := u) hd hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for heat-shear initial data with full constant drift on `ℝ^3`
whenever the streamwise drift is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearFullDriftInitialVelocity a k d c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearFullDriftInitialVelocity a k d c) :=
    smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity hd
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to the full-drift heat-shear
datum on every nonnegative slab whenever the streamwise drift is nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the full-drift
heat-shear field is an exact smooth incompressible candidate with explicit slab
vorticity bound `|a * k|`; bounded kinetic energy is the only missing witness
slot. -/
theorem heatShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearFullDriftVelocityField ν a k d c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearFullDriftVelocityField ν a k d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure ν a k d c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearFullDriftVelocityField ν a k d c t x
  · exact matchesInitialVelocity_heatShearFullDriftVelocityField ν a k d c
  · exact uniformVorticityBoundUpTo_heatShearFullDriftVelocityField ν a k d c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd hT

/-- Heat shear with full constant drift exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT

/-- The repaired explicit regularity clause is likewise vacuous on full-drift
heat-shear data with nonzero streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearFullDriftInitialVelocity a k d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired explicit regularity clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The structured fully concrete clause also rejects full-drift heat-shear
initial data with nonzero streamwise drift. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity
    {ν : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity a k d c
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity hd
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearFullDriftInitialVelocity a k d c)
        hν
        (smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x)).mp
        hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for full-drift heat-shear initial data with nonzero streamwise
drift because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The repaired uniform-vorticity continuation clause is also vacuous on
full-drift heat-shear data with nonzero streamwise drift because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired uniform-vorticity clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The transported heat-shear field is likewise an honest exact candidate on
the global explicit theorem surface; with nonzero transport speed, bounded
kinetic energy is the only missing witness slot. -/
theorem heatShearTransportVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k b : ℝ} (hb : b ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearTransportVelocityField ν a k b, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure ν a k b t x
  · intro t x
    simpa using spatialDivergence_heatShearTransportVelocityField ν a k b t x
  · exact matchesInitialVelocity_heatShearTransportVelocityField ν a k b
  · exact not_boundedKineticEnergy_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb

/-- Transported heat shear therefore exhibits the same exact mismatch on the
global explicit theorem surface: an honest smooth PDE-side candidate exists,
but the explicit global-output proposition is still false because bounded
kinetic energy fails. -/
theorem heatShearTransportInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k b : ℝ} (hb : b ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (b := b) hb
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
        (u := u) hb hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
transported heat-shear initial data whenever the transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearTransportInitialVelocity a k b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportInitialVelocity
      (u := u) hb hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for transported heat-shear initial data on `ℝ^3` whenever the
transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearTransportInitialVelocity a k b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearTransportInitialVelocity a k b) :=
    smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
  have hdiv : ∀ x, initialSpatialDivergence (heatShearTransportInitialVelocity a k b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity hb
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to transported heat-shear data
on every nonnegative slab whenever the transport speed is nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the transported
heat-shear field is an exact smooth incompressible candidate with explicit slab
vorticity bound `|a * k|`; bounded kinetic energy is the only missing witness
slot. -/
theorem heatShearTransportVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearTransportVelocityField ν a k b, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure ν a k b t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearTransportVelocityField ν a k b t x
  · exact matchesInitialVelocity_heatShearTransportVelocityField ν a k b
  · exact uniformVorticityBoundUpTo_heatShearTransportVelocityField ν a k b T hν
  · exact not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
      (ν := ν) (a := a) (k := k) (b := b) hb hT

/-- Transported heat shear exposes the same exact gap on the explicit
uniform-vorticity surface: there is an exact smooth incompressible candidate
with a uniform slab vorticity bound, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT

/-- The repaired explicit regularity clause is likewise vacuous on transported
heat-shear data with nonzero transport speed because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportInitialVelocity a k b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired explicit regularity clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity_without_regularity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity
      (ν := ν) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The structured fully concrete clause also rejects transported heat-shear
initial data with nonzero transport speed. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity
    {ν : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity a k b
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity hb
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportInitialVelocity a k b)
        hν
        (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x)).mp
        hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for transported heat-shear initial data with nonzero transport
speed because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The repaired uniform-vorticity continuation clause is also vacuous on
transported heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired uniform-vorticity clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The transported full-drift heat-shear field is likewise an honest exact
candidate on the global explicit theorem surface; with nonzero transport
speed, bounded kinetic energy is the only missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      ¬ boundedKineticEnergy u := by
  refine ⟨heatShearTransportFullDriftVelocityField ν a k b d c, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    simpa using momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure ν a k b d c t x
  · intro t x
    simpa using spatialDivergence_heatShearTransportFullDriftVelocityField ν a k b d c t x
  · exact matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · exact not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb

/-- Transported full-drift heat shear therefore exposes the same exact
mismatch on the global explicit theorem surface: an honest smooth PDE-side
candidate exists, but the explicit global-output proposition is still false
because bounded kinetic energy fails. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
    {ν a k b d c : ℝ} (hb : b ≠ 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_concreteCandidate_except_boundedEnergy
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · intro hOut
    rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    exact
      not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
        (u := u) hb hinit hbd

/-- The fully explicit global-output surface is likewise impossible for
transported full-drift heat-shear initial data whenever the transport speed is
nonzero. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_heatShearTransportFullDriftInitialVelocity
      (u := u) hb hinit hbd

/-- At positive viscosity, the explicit concrete regularity clause is therefore
also impossible for transported full-drift heat-shear initial data on `ℝ^3`
whenever the transport speed is nonzero. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (heatShearTransportFullDriftInitialVelocity a k b d c) :=
    smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
  have hdiv : ∀ x, initialSpatialDivergence (heatShearTransportFullDriftInitialVelocity a k b d c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity hb
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- The same witness-level obstruction applies to transported full-drift
heat-shear data on every nonnegative slab whenever the transport speed is
nonzero. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)
      hT

/-- On every nonnegative slab with nonnegative viscosity, the transported
full-drift heat-shear field is an exact smooth incompressible candidate with
explicit slab vorticity bound `|a * k|`; bounded kinetic energy is the only
missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨heatShearTransportFullDriftVelocityField ν a k b d c, 0, |a * k|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x ht0 htT
    simpa using momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure ν a k b d c t x
  · intro t x ht0 htT
    simpa using spatialDivergence_heatShearTransportFullDriftVelocityField ν a k b d c t x
  · exact matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c
  · exact uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField ν a k b d c T hν
  · exact not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- Transported full-drift heat shear exposes the same exact gap on the
explicit uniform-vorticity surface: there is an exact smooth incompressible
candidate with a uniform slab vorticity bound, but the finite-time witness
type is still empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- The repaired explicit regularity clause is likewise vacuous on transported
full-drift heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired explicit regularity clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
unrepaired concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The structured fully concrete clause also rejects transported full-drift
heat-shear initial data with nonzero transport speed. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity
    {ν : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity hb
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
        hν
        (smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x)).mp
        hClause)

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for transported full-drift heat-shear initial data with nonzero
transport speed because the finite-time witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The repaired uniform-vorticity continuation clause is also vacuous on
transported full-drift heat-shear data with nonzero transport speed because
the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired uniform-vorticity clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
trivially satisfied for nonzero constant initial data because the quantified
finite-time witness type is already uninhabited there.  This records a genuine
target-shape caveat, not analytic progress. -/
theorem ExplicitUniformVorticityContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := constantInitialVelocity c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT)

/-- The uniform continuation clause can therefore be true on nonzero constant
initial data even though the concrete regularity clause is false there. -/
theorem ExplicitUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nonzero constant initial data because the repaired finite-energy hypothesis
already fails.  Again, no horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (constantInitialVelocity c) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired uniform-vorticity continuation clause can therefore also be
true on nonzero constant initial data while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- Any fully explicit global smooth solution yields a finite-time witness on
every slab `0 ≤ t ≤ T`. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.implies_finiteTimeWitness
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T) := by
  rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  refine ⟨{
    velocity := u
    pressure := p
    smooth_velocity := hu
    smooth_pressure := hp
    momentum_equation_on := ?_
    incompressible_on := ?_
    initial_condition := hinit
    bounded_energy_on := boundedKineticEnergy_implies_boundedKineticEnergyUpTo hbd
  }⟩
  · intro t x ht0 htT
    exact hmom t x
  · intro t x ht0 htT
    exact hinc t x

/-- Pressure-gauge symmetry on finite-time witnesses: adding a spatially and
slice-wise zero-gradient pressure field leaves the witness valid on the same
slab. -/
def ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
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
    rw [spatialPressureGradient_add hp hq', hq_zero]
    simpa using W.momentum_equation_on t x ht0 htT
  incompressible_on := W.incompressible_on
  initial_condition := W.initial_condition
  bounded_energy_on := W.bounded_energy_on

/-- Pressure-gauge symmetry on finite-time witnesses: adding a spatially and
temporally constant pressure leaves the witness valid on the same slab. -/
def ExplicitFiniteTimeRegularityWitness.addConstantPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (c : ℝ) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  W.addPressureOfZeroSpatialGradient
    (fun _ : NSTime => fun _ : NSSpace => c)
    (smoothSpaceTimePressure_const c)
    (fun t x => spatialPressureGradient_const c t x)

/-- Pressure-gauge symmetry on finite-time witnesses: adding any smooth
time-only pressure leaves the witness valid on the same slab. -/
def ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  W.addPressureOfZeroSpatialGradient
    (fun t : NSTime => fun _ : NSSpace => π t)
    (smoothSpaceTimePressure_timeOnly hπ)
    (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Uniform vorticity control is unchanged under adding any smooth pressure
gauge with zero spatial gradient on each slice, since the velocity field is
unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    uniformVorticityBoundUpTo
      (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hω

/-- Uniform vorticity control is unchanged under adding a smooth time-only
pressure gauge to a finite-time witness, since the velocity field is unchanged.
-/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    uniformVorticityBoundUpTo (W.addTimeOnlyPressure π hπ).velocity T B := by
  exact
    W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Uniform vorticity control remains available after adding a smooth
zero-spatial-gradient pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo
      ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity T' B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
    ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_restrict
      (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)

/-- Uniform vorticity control remains available after adding a smooth time-only
pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    uniformVorticityBoundUpTo ((W.addTimeOnlyPressure π hπ).restrict hT).velocity T' B := by
  exact
    W.uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Pressure-gauge symmetry on the explicit global output surface: adding a
slice-wise zero-gradient pressure field preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  refine ⟨u, p + q, hu, ?_, ?_, hinc, hinit, hbd⟩
  · exact smoothSpaceTimePressure_add hp hq
  · intro t x
    have hp' :
        DifferentiableAt ℝ (fun y : NSSpace => p t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
    have hq' :
        DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
    rw [spatialPressureGradient_add hp' hq', hq_zero]
    simpa using hmom t x

/-- Pressure-gauge symmetry on the explicit global output surface: adding a
spatially and temporally constant pressure preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addConstantPressure
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact h.addPressureOfZeroSpatialGradient
    (fun _ : NSTime => fun _ : NSSpace => c)
    (smoothSpaceTimePressure_const c)
    (fun t x => spatialPressureGradient_const c t x)

/-- Pressure-gauge symmetry on the explicit global output surface: adding any
smooth time-only pressure preserves a global solution. -/
theorem ExplicitConcreteNavierStokesGlobalOutput.addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact h.addPressureOfZeroSpatialGradient
    (fun t : NSTime => fun _ : NSSpace => π t)
    (smoothSpaceTimePressure_timeOnly hπ)
    (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Pressure-gauge symmetry on the explicit whole-space regularity clause:
adding a slice-wise zero-gradient pressure field preserves the clause on the
same initial datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h hν hsmooth hdiv) q hq hq_zero

/-- Pressure-gauge symmetry on the repaired explicit whole-space regularity
clause: adding a slice-wise zero-gradient pressure field preserves the clause
on the same finite-energy datum. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv hfinite
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h hν hsmooth hdiv hfinite) q hq hq_zero

/-- Pressure-gauge symmetry on the structured fully concrete whole-space
clause: adding a slice-wise zero-gradient pressure field preserves the clause
on the same datum. -/
theorem concreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv })
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  have hGlobal : ExplicitConcreteNavierStokesGlobalOutput ν u₀ :=
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
      hν hsmooth hdiv
      (hGlobal.addPressureOfZeroSpatialGradient q hq hq_zero)

/-- Pressure-gauge symmetry on the repaired structured fully concrete
whole-space clause: adding a slice-wise zero-gradient pressure field preserves
the clause on the same finite-energy datum. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hGlobal : ExplicitConcreteNavierStokesGlobalOutput ν u₀ :=
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mp h hν hsmooth hdiv hfinite
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite
      (hGlobal.addPressureOfZeroSpatialGradient q hq hq_zero)

/-- A uniform-vorticity continuation clause can be applied equally well after
changing the witness by any smooth pressure gauge with zero spatial gradient,
since the carried uniform vorticity bound is pressure-invariant. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hω' :
      ∃ B' : ℝ,
        uniformVorticityBoundUpTo
          (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T B' := by
    refine ⟨B, ?_⟩
    exact W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω q hq hq_zero
  exact hClause hν hsmooth hdiv (W.addPressureOfZeroSpatialGradient q hq hq_zero) hω'

/-- A uniform-vorticity continuation clause can be applied equally well after
changing the witness by a smooth time-only pressure gauge, since the carried
uniform vorticity bound is pressure-invariant. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied
after first changing a larger-slab witness by a smooth zero-spatial-gradient
pressure gauge and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict,
    ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using
    (ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv (W := W.restrict hT)
      (hω := W.uniformVorticityBound_restrict hω hT) q hq hq_zero)

/-- A uniform-vorticity continuation clause at horizon `T'` can be applied
after first changing a larger-slab witness by a smooth time-only pressure gauge
and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitUniformVorticityContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Zero initial velocity data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_zero :
    smoothInitialVelocityData (0 : NSInitialVelocity) := by
  simpa [smoothInitialVelocityData] using (contDiff_const : ContDiff ℝ ∞ (0 : NSInitialVelocity))

/-- Canonical finite-time witness on any slab for zero initial data. -/
def zeroFiniteTimeRegularityWitness (ν T : ℝ) :
    ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T where
  velocity := 0
  pressure := 0
  smooth_velocity := by
    simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
  smooth_pressure := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  momentum_equation_on := by
    intro t x ht0 htT
    have hu0 : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x := by
      simpa using
        (contDiffAt_const : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x)
    have hlap0 : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa using
        (spatialLaplacian_const_smul (a := (0 : ℝ)) (u := (0 : NSVelocityField))
          (t := t) (x := x) hu0)
    simp [hlap0, timeVelocityDerivative_zero, spatialPressureGradient_zero,
      spatialConvection, spatialFDeriv]
  incompressible_on := by
    intro t x ht0 htT
    simpa using (spatialDivergence_zero t x)
  initial_condition := by
    intro x
    rfl
  bounded_energy_on := by
    refine ⟨0, le_rfl, ?_⟩
    intro t ht0 htT
    constructor
    · have hk :
        kineticEnergyDensity (0 : NSVelocityField) t =
          (fun _ : NSSpace => (0 : ℝ)) := by
        funext x
        simp [kineticEnergyDensity]
      rw [hk]
      exact
        (MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
    · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
        simp [kineticEnergyAt, kineticEnergyDensity]
      simp [hE0]

/-- The canonical zero witness has a uniform zero vorticity bound on every slab.
-/
theorem zeroFiniteTimeRegularityWitness_has_uniformVorticityBound
    (ν T : ℝ) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo (zeroFiniteTimeRegularityWitness ν T).velocity T B := by
  refine ⟨0, ?_⟩
  simpa [zeroFiniteTimeRegularityWitness] using (uniformVorticityBoundUpTo_zero T)

/-- The zero witness gives an honest inhabited premise for the concrete uniform
continuation clause on every slab.  This is the basic nonvacuity baseline that
contrasts with the impossible nonzero constant-initial-data cases. -/
theorem zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise
    (ν T : ℝ) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  refine ⟨zeroFiniteTimeRegularityWitness ν T, ?_⟩
  exact zeroFiniteTimeRegularityWitness_has_uniformVorticityBound ν T

/-- Concrete finite-slab gauge baseline: after adding any smooth time-only
pressure to the zero witness on a larger slab and restricting to a shorter one,
the resulting witness still carries the explicit zero uniform-vorticity bound.
-/
theorem zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
    (ν Tsmall Tlarge : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
        Tsmall B := by
  refine ⟨0, ?_⟩
  exact
    (zeroFiniteTimeRegularityWitness ν Tlarge).uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (by
        simpa [zeroFiniteTimeRegularityWitness] using
          (uniformVorticityBoundUpTo_zero Tlarge))
      q hq hq_zero hT

/-- Time-only special case of the zero-data zero-spatial-gradient gauge
baseline on restricted slabs. -/
theorem zeroFiniteTimeRegularityWitness_addTimeOnlyPressure_restrict_has_uniformVorticityBound
    (ν Tsmall Tlarge : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        (((zeroFiniteTimeRegularityWitness ν Tlarge).addTimeOnlyPressure π hπ).restrict hT).velocity
        Tsmall B := by
  exact
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Concrete bottom-up baseline: zero initial data admit an explicit global
smooth Navier--Stokes witness (the zero velocity/pressure pair). -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero
    (ν : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : NSSpace)))
  · simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  · intro t x
    have hu0 : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x := by
      simpa using
        (contDiffAt_const : ContDiffAt ℝ 2 (fun y : NSSpace => (0 : NSSpace)) x)
    have hlap0 : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa using
        (spatialLaplacian_const_smul (a := (0 : ℝ)) (u := (0 : NSVelocityField))
          (t := t) (x := x) hu0)
    simp [hlap0, timeVelocityDerivative_zero, spatialPressureGradient_zero,
      spatialConvection, spatialFDeriv]
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
        (MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
    · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
        simp [kineticEnergyAt, kineticEnergyDensity]
      simp [hE0]

/-- Zero initial data satisfy the repaired finite-energy admissibility
hypothesis on `ℝ^3`. -/
theorem finiteInitialKineticEnergy_zero :
    finiteInitialKineticEnergy (0 : NSInitialVelocity) := by
  have hzero :
      initialKineticEnergyDensity (0 : NSInitialVelocity) =
        (fun _ : NSSpace => (0 : ℝ)) := by
    funext x
    simp [initialKineticEnergyDensity]
  rw [finiteInitialKineticEnergy, hzero]
  exact
    MeasureTheory.integrable_zero NSSpace ℝ
      (MeasureTheory.volume : MeasureTheory.Measure NSSpace)

/-- Concrete nonzero-pressure baseline: zero velocity with any constant
pressure still gives a global explicit Navier--Stokes output. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitConcreteNavierStokesGlobalOutput_zero ν) q hq hq_zero

/-- Constant-pressure special case of the generic zero-data zero-gradient
pressure transport on the explicit whole-space output layer. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_constantPressure
    (ν c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- Concrete time-gauge baseline: zero velocity with any smooth time-only
pressure still gives a global explicit Navier--Stokes output. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The concrete regularity clause is directly inhabitable at zero initial data.
-/
theorem ExplicitConcreteNavierStokesRegularityClause_zero
    (ν : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the explicit unrepaired
regularity-clause surface. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
      (ExplicitConcreteNavierStokesRegularityClause_zero ν) q hq hq_zero

/-- The concrete regularity clause remains directly inhabitable at zero initial
data after adding any constant pressure gauge. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_constantPressure
    (ν c : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The concrete regularity clause remains directly inhabitable at zero initial
data after adding any smooth time-only pressure gauge. -/
theorem ExplicitConcreteNavierStokesRegularityClause_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The structured fully concrete clause is directly inhabitable at zero
initial data by converting the explicit zero solution through the concrete
equivalence theorem. -/
theorem concreteNavierStokesGlobalRegularityClause_zero
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
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the structured fully
concrete whole-space clause. -/
theorem concreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
    {ν : ℝ} (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact
    concreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      (concreteNavierStokesGlobalRegularityClause_zero hν)
      q hq hq_zero

/-- The repaired explicit finite-energy theorem surface is likewise directly
inhabited at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero
    (ν : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the repaired explicit
finite-energy regularity-clause surface. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
    (ν : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_addPressureOfZeroSpatialGradient
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν) q hq hq_zero

/-- The repaired explicit finite-energy regularity clause remains directly
inhabitable at zero initial data after adding any constant pressure gauge. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_constantPressure
    (ν c : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The repaired explicit finite-energy regularity clause remains directly
inhabitable at zero initial data after adding any smooth time-only pressure
gauge. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The repaired structured fully concrete clause is likewise directly
inhabitable at zero initial data. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      (ν := ν) (u₀ := (0 : NSInitialVelocity))
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      finiteInitialKineticEnergy_zero
      (ExplicitConcreteNavierStokesGlobalOutput_zero ν)

/-- Generic zero-data pressure-gauge transport on the repaired structured fully
concrete whole-space clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
    {ν : ℝ} (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_addPressureOfZeroSpatialGradient
      hν smoothInitialVelocityData_zero
      (by
        intro x
        simpa using (initialSpatialDivergence_zero x))
      finiteInitialKineticEnergy_zero
      (finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero hν)
      q hq hq_zero

/-- The unrepaired uniform-vorticity continuation clause is directly
inhabitable at zero initial data: any finite-time witness on the zero datum may
be discarded in favor of the explicit global zero solution. -/
theorem ExplicitUniformVorticityContinuationClause_zero
    (ν T : ℝ) :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  intro _hν _hsmooth _hdiv _W _hω
  exact ExplicitConcreteNavierStokesGlobalOutput_zero ν

/-- The repaired finite-energy uniform-vorticity continuation clause is
likewise directly inhabitable at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_zero
    (ν T : ℝ) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  intro _hν _hsmooth _hdiv _hfinite _W _hω
  exact ExplicitConcreteNavierStokesGlobalOutput_zero ν

/-- Clause-level operational consequence at zero initial data: applying one
uniform-vorticity continuation clause instance to the canonical zero slab
witness yields an explicit global output. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise ν T with
    ⟨W, hω⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 W hω

/-- Nontrivial operational pressure-gauge sanity check: a smaller-slab uniform
continuation clause can be applied to a larger zero witness after adding any
smooth time-only pressure gauge and restricting back down. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hω :
      ∃ B : ℝ,
        uniformVorticityBoundUpTo
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall B :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hω

/-- Time-only special case of the zero-data uniform clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the uniform clause-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- Operational consequence of the uniform-vorticity target: for positive
viscosity, applying the target to the canonical zero slab witness yields a
global explicit output for zero initial data. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T :=
    hTarget ν (0 : NSInitialVelocity) T
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level operational pressure-gauge sanity check on the unrepaired
uniform-vorticity layer: the target applies on any smaller zero slab after
adding a smooth time-only pressure gauge on a larger zero witness and
restricting back down. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hTarget ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the zero-data uniform target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hTarget hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the uniform target-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hTarget hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- If the horizon is negative, the slab conditions `0 ≤ t ≤ T` are empty, so
steady linear shear itself furnishes a formal finite-time witness. This
exposes the missing `0 ≤ T` hypothesis in the unrepaired continuation target.
-/
def explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
    {ν T a : ℝ}
    (hT : T < 0) :
    ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T where
  velocity := linearShearVelocityField a
  pressure := 0
  smooth_velocity := smoothSpaceTimeVelocity_linearShearVelocityField a
  smooth_pressure := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  momentum_equation_on := by
    intro t x ht0 htT'
    exfalso
    linarith
  incompressible_on := by
    intro t x ht0 htT'
    exfalso
    linarith
  initial_condition := matchesInitialVelocity_linearShearVelocityField a
  bounded_energy_on := by
    refine ⟨0, le_rfl, ?_⟩
    intro t ht0 htT'
    exfalso
    linarith

/-- The unrepaired uniform-vorticity continuation target is false as stated.
For a negative horizon, nonzero linear shear admits a formal finite-time witness
with uniform vorticity bound, while the required global bounded-energy output is
already impossible on `ℝ^3`. -/
theorem not_ExplicitUniformVorticityContinuationTarget :
    ¬ ExplicitUniformVorticityContinuationTarget := by
  intro hTarget
  have hν : 0 < (1 : ℝ) := by positivity
  have hdiv :
      ∀ x, initialSpatialDivergence (linearShearInitialVelocity 1) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x
  let W : ExplicitFiniteTimeRegularityWitness 1 (linearShearInitialVelocity 1) (-1) :=
    explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
      (ν := 1) (T := -1) (a := 1) (by norm_num)
  have hω : ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity (-1) B := by
    refine ⟨1, ?_⟩
    simpa [W, explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero] using
      (uniformVorticityBoundUpTo_linearShearVelocityField (a := (1 : ℝ)) (-1))
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity one_ne_zero
      (hTarget 1 (linearShearInitialVelocity 1) (-1)
        hν
        (smoothInitialVelocityData_linearShearInitialVelocity 1)
        hdiv W hω)

/-- Clause-level operational consequence for the repaired finite-energy
uniform-vorticity layer: zero initial data satisfy the repaired input
hypothesis directly, so a repaired clause instance can be applied to the
canonical zero slab witness without vacuity. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise ν T with
    ⟨W, hω⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero W hω

/-- Nontrivial operational pressure-gauge sanity check on the repaired
finite-energy uniform-vorticity layer: a smaller-slab repaired clause can be
applied to a larger zero witness after adding any smooth time-only pressure
gauge and restricting back down. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hω :
      ∃ B : ℝ,
        uniformVorticityBoundUpTo
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall B :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hω

/-- Time-only special case of the repaired zero-data uniform clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired uniform clause-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The repaired finite-energy uniform-vorticity continuation target is also
operational at zero initial data: the zero datum satisfies the repaired input
hypothesis directly, so the target applies to the canonical zero slab witness
without any vacuity. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause :
      ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T :=
    hTarget ν (0 : NSInitialVelocity) T
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level repaired time-gauge sanity check: the repaired finite-energy
uniform-vorticity target applies on any smaller zero slab after adding a smooth
time-only pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause :
      ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (0 : NSInitialVelocity) Tsmall :=
    hTarget ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the repaired zero-data uniform target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hTarget hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired uniform target-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hTarget hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The fully explicit NS theorem target subsumes the uniform-vorticity
continuation target.  This is only a one-way sanity theorem: the current proof
reuses the global theorem target directly and does not yet use the finite-time
witness or vorticity-bound hypothesis analytically. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _W _hω
  exact h hν hsmooth hdiv

/-- The repaired explicit whole-space regularity clause likewise yields the
repaired fixed-horizon uniform-vorticity continuation clause on the same datum.
-/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite _W _hω
  exact h hν hsmooth hdiv hfinite

/-- The same explicit whole-space regularity clause also yields the whole
fixed-datum family of uniform-vorticity continuation clauses, one for each
horizon. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
      (T := T) h

/-- Likewise, the repaired explicit whole-space regularity clause yields the
whole fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
      (T := T) h

/-- The fully explicit NS theorem target subsumes the uniform-vorticity
continuation target.  This is only a one-way sanity theorem: the current proof
reuses the global theorem target directly and does not yet use the finite-time
witness or vorticity-bound hypothesis analytically. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  intro ν u₀
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of uniform-vorticity continuation clauses directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also gives the corresponding
fixed-horizon uniform-vorticity continuation clause directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The original continuation clause immediately implies the repaired
finite-energy version, since the extra input hypothesis is only a restriction
on admissible data. -/
theorem ExplicitUniformVorticityContinuationClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _hfinite W hω
  exact hClause hν hsmooth hdiv W hω

/-- The same lift also holds on the theorem surface: an unrepaired
uniform-vorticity target immediately implies the repaired one, because the
extra finite-energy input is only an admissibility restriction. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hUniform : ExplicitUniformVorticityContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy (hUniform ν u₀ T)

/-- On a nonnegative slab, the repaired and unrepaired uniform-vorticity
continuation clauses coincide: any actual finite-time witness already forces
finite initial kinetic energy. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T ↔
      ExplicitUniformVorticityContinuationClause ν u₀ T := by
  constructor
  · intro hClause hν hsmooth hdiv W hω
    exact hClause hν hsmooth hdiv (W.finiteInitialKineticEnergy hT) W hω
  · intro hClause
    exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy hClause

/-- The repaired explicit finite-energy theorem surface directly implies the
repaired uniform-vorticity continuation target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)

/-- On a nonnegative slab, the repaired uniform-vorticity clause can be read as
the original unrepaired clause, because any actual finite-time witness already
supplies the missing finite-energy hypothesis. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon hT).mp
      hClause

/-- Hence the repaired uniform-vorticity target also forgets directly to the
unrepaired clause at each fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (hClause := hUniform ν u₀ T) hT

/-- The repaired uniform-vorticity target also forgets to the unrepaired
uniform clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (hClause := hUniform ν u₀ hT) hT

/-- The repaired explicit finite-energy theorem surface proves the corrected
nonnegative-horizon continuation target directly. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTargetOnNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T _hT
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (h ν u₀)) T

/-- The repaired uniform-vorticity target also forgets to the unrepaired
uniform clause family on every nonnegative horizon. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hUniform : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hUniform hT

/-- The repaired explicit finite-energy theorem surface also directly implies
the repaired uniform-vorticity continuation clause at each fixed horizon. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface as a
fixed-datum all-horizons family. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface at a
fixed horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Since the unrepaired explicit theorem surface subsumes the repaired
finite-energy theorem surface, it also directly subsumes the repaired
uniform-vorticity continuation target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired uniform-vorticity continuation clauses. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- Likewise, the unrepaired explicit theorem surface directly subsumes the
repaired uniform-vorticity continuation clause at each fixed horizon. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of repaired uniform clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface still implies the
uniform-vorticity continuation clause on every nonnegative slab.  Finite-energy
inputs are handled by the repaired target directly; non-finite-energy inputs
cannot support a finite-time witness there in the first place. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTargetOnNonnegHorizons
        h)

/-- The repaired explicit finite-energy theorem surface still implies the
uniform-vorticity continuation clause on every nonnegative slab.  Finite-energy
inputs are handled by the repaired target directly; non-finite-energy inputs
cannot support a finite-time witness there in the first place. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the structured fully concrete theorem target subsumes the same
uniform-vorticity continuation target via the explicit-target equivalence.
Again, this is only a subsumption theorem, not a continuation proof. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h))

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of unrepaired uniform clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The explicit whole-space theorem target is operational at zero initial
data: positive viscosity and the canonical zero datum satisfy the input side
directly, so the target yields a concrete global output there. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  exact h ν (0 : NSInitialVelocity) hν smoothInitialVelocityData_zero hdiv0

/-- Zero-data pressure-gauge transport on the explicit whole-space theorem
surface: once the theorem target yields the canonical zero global output, any
smooth slice-wise zero-spatial-gradient pressure gauge may be added directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν)
      q hq hq_zero

/-- Time-only pressure-gauge special case of the explicit whole-space theorem
target at zero initial data. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the explicit whole-space theorem target
at zero initial data. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The structured whole-space theorem target has the same zero-data
operational consequence via the explicit equivalence theorem. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h) hν

/-- Zero-data pressure-gauge transport on the structured unrepaired
whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h) hν q hq hq_zero

/-- Time-only pressure-gauge special case of the structured whole-space theorem
target at zero initial data. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the structured whole-space theorem target
at zero initial data. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The repaired explicit finite-energy theorem target is likewise operational
at zero initial data, since the zero datum is finite-energy. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  exact
    h ν (0 : NSInitialVelocity) hν smoothInitialVelocityData_zero hdiv0
      finiteInitialKineticEnergy_zero

/-- Zero-data pressure-gauge transport on the repaired explicit whole-space
theorem surface. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput.addPressureOfZeroSpatialGradient
      (h := ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
        h hν)
      q hq hq_zero

/-- Time-only pressure-gauge special case of the repaired explicit finite-energy
theorem target at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the repaired explicit finite-energy
theorem target at zero initial data. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

/-- The structured repaired finite-energy theorem target has the same zero-data
operational consequence via the explicit equivalence theorem. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h) hν

/-- Zero-data pressure-gauge transport on the structured repaired
whole-space theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h) hν q hq hq_zero

/-- Time-only pressure-gauge special case of the structured repaired
finite-energy theorem target at zero initial data. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- Constant-pressure special case of the structured repaired finite-energy
theorem target at zero initial data. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
