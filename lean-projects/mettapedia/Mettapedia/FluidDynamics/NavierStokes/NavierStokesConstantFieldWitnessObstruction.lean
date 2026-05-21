import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Constant-field finite-time witness obstruction

This file isolates the exact failure mode of the nonzero constant-field ansatz
on the fully concrete whole-space finite-time witness surface.

On `ℝ × ℝ^3`, a nonzero constant velocity field with any smooth zero-spatial-
gradient pressure gauge satisfies the smoothness, momentum, incompressibility,
and initial-condition fields of `ExplicitFiniteTimeRegularityWitness`.
But it can never satisfy the bounded-energy slot on any nonnegative slab,
because its kinetic-energy density is a positive constant on the infinite
spatial domain.

So the tempting steady exact solution is blocked by one honest concrete field of
the witness record, not by an interface mismatch.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConstantFieldWitnessObstruction

/-- A constant velocity field with any smooth slice-wise zero-spatial-gradient
pressure gauge satisfies every finite-time witness field except bounded energy.
-/
theorem constantVelocityField_zeroSpatialGradientPressure_nonEnergyFiniteTimeFields
    {ν T : ℝ} (c : NSSpace) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    smoothSpaceTimeVelocity (constantVelocityField c) ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative (constantVelocityField c) t x +
            spatialConvection (constantVelocityField c) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (constantVelocityField c) t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T ->
        spatialDivergence (constantVelocityField c) t x = 0) ∧
      MatchesInitialVelocity
        (constantInitialVelocity c) (constantVelocityField c) := by
  refine ⟨smoothSpaceTimeVelocity_constantVelocityField c, hp, ?_, ?_, ?_⟩
  · intro t x _ht0 _htT
    rw [timeVelocityDerivative_constantVelocityField,
      spatialConvection_constantVelocityField,
      hp_zero t x,
      spatialLaplacian_constantVelocityField]
    simp
  · intro t x _ht0 _htT
    simpa using spatialDivergence_constantVelocityField c t x
  · exact matchesInitialVelocity_constantVelocityField c

/-- A nonzero constant velocity field can never appear as the exact velocity of
an honest finite-time witness on a nonnegative slab, regardless of which
pressure field is paired with it, because the bounded-energy slot fails. -/
theorem not_exists_constantVelocityField_finiteTimeWitness_of_nonzero
    {ν T : ℝ} {c : NSSpace} {p : NSPressureField}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T,
        W.velocity = constantVelocityField c ∧ W.pressure = p := by
  intro hW
  rcases hW with ⟨W, hvel, _hpress⟩
  have hE : boundedKineticEnergyUpTo (constantVelocityField c) T := by
    simpa [hvel] using W.bounded_energy_on
  exact not_boundedKineticEnergyUpTo_constantVelocityField hc hT hE

/-- Candidate-level obstruction for the nonzero constant-field ansatz with a
smooth time-only pressure gauge: all non-energy witness fields are present, but
the exact finite-time witness does not exist because the bounded-energy slot
fails on `ℝ^3`. -/
theorem constantVelocityField_timeOnlyPressure_exhibits_nonEnergyFiniteTimeFields_without_exactWitness
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (smoothSpaceTimeVelocity (constantVelocityField c) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative (constantVelocityField c) t x +
            spatialConvection (constantVelocityField c) t x +
            spatialPressureGradient (fun t : NSTime => fun _ : NSSpace => π t) t x =
          ν • spatialLaplacian (constantVelocityField c) t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T ->
        spatialDivergence (constantVelocityField c) t x = 0) ∧
      MatchesInitialVelocity
        (constantInitialVelocity c) (constantVelocityField c)) ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T,
          W.velocity = constantVelocityField c ∧
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  refine ⟨?_, ?_⟩
  · exact
      constantVelocityField_zeroSpatialGradientPressure_nonEnergyFiniteTimeFields
        (ν := ν) (T := T) c
        (fun t : NSTime => fun _ : NSSpace => π t)
        (smoothSpaceTimePressure_timeOnly hπ)
        (fun t x => spatialPressureGradient_timeOnly π t x)
  · exact not_exists_constantVelocityField_finiteTimeWitness_of_nonzero hc hT

end ConstantFieldWitnessObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
