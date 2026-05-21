import Mettapedia.FluidDynamics.NavierStokes.NavierStokesConstantFieldWitnessObstruction

/-!
# Regression tests for the constant-field finite-time witness obstruction
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace NavierStokesConstantFieldWitnessObstructionRegression

/-- A concrete nonzero constant velocity used to test the whole-space
bounded-energy obstruction. -/
def constantFieldWitnessObstructionVelocity : NSSpace :=
  EuclideanSpace.single nsCoord1 (1 : ℝ)

theorem constantFieldWitnessObstructionVelocity_ne_zero :
    constantFieldWitnessObstructionVelocity ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord1) h
  simp [constantFieldWitnessObstructionVelocity] at h1

theorem constant_field_time_only_pressure_nonEnergy_fields_regression
    {ν T : ℝ}
    (hT : 0 ≤ T) :
    smoothSpaceTimeVelocity (constantVelocityField constantFieldWitnessObstructionVelocity) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => t + 1) ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative (constantVelocityField constantFieldWitnessObstructionVelocity) t x +
            spatialConvection (constantVelocityField constantFieldWitnessObstructionVelocity) t x +
            spatialPressureGradient (fun t : NSTime => fun _ : NSSpace => t + 1) t x =
          ν • spatialLaplacian (constantVelocityField constantFieldWitnessObstructionVelocity) t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T ->
        spatialDivergence (constantVelocityField constantFieldWitnessObstructionVelocity) t x = 0) ∧
      MatchesInitialVelocity
        (constantInitialVelocity constantFieldWitnessObstructionVelocity)
        (constantVelocityField constantFieldWitnessObstructionVelocity) := by
  exact
    (constantVelocityField_timeOnlyPressure_exhibits_nonEnergyFiniteTimeFields_without_exactWitness
      (ν := ν)
      (T := T)
      (c := constantFieldWitnessObstructionVelocity)
      constantFieldWitnessObstructionVelocity_ne_zero
      hT
      (fun t : NSTime => t + 1)
      (by simpa using (contDiff_id.add contDiff_const))).1

theorem constant_field_time_only_pressure_no_exact_witness_regression
    {ν T : ℝ}
    (hT : 0 ≤ T) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (constantInitialVelocity constantFieldWitnessObstructionVelocity) T,
        W.velocity = constantVelocityField constantFieldWitnessObstructionVelocity ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => t + 1) := by
  exact
    (constantVelocityField_timeOnlyPressure_exhibits_nonEnergyFiniteTimeFields_without_exactWitness
      (ν := ν)
      (T := T)
      (c := constantFieldWitnessObstructionVelocity)
      constantFieldWitnessObstructionVelocity_ne_zero
      hT
      (fun t : NSTime => t + 1)
      (by simpa using (contDiff_id.add contDiff_const))).2

end NavierStokesConstantFieldWitnessObstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
