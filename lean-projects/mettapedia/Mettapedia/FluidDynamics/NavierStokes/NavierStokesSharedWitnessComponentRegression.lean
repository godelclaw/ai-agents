import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSharedWitnessComponent

/-!
# Regression tests for the shared-witness component clause
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace NavierStokesSharedWitnessComponentRegression

/-- A concrete nonzero constant velocity whose first component vanishes. -/
def splitSharedWitnessCounterexampleVelocity : NSSpace :=
  EuclideanSpace.single nsCoord1 (1 : ℝ)

theorem splitSharedWitnessCounterexampleVelocity_ne_zero :
    splitSharedWitnessCounterexampleVelocity ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord1) h
  simp [splitSharedWitnessCounterexampleVelocity] at h1

theorem splitSharedWitnessCounterexampleVelocity_component_zero :
    splitSharedWitnessCounterexampleVelocity nsCoord0 = 0 := by
  have hne : nsCoord0 ≠ nsCoord1 := by decide
  simp [splitSharedWitnessCounterexampleVelocity, hne]

theorem zero_initial_velocity_sharedWitness_component_regression
    {ν : ℝ} (hν : 0 < ν) :
    SharedWitnessComponentRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) }
      nsCoord0 := by
  exact
    (sharedWitnessComponentRegularityClause_iff_globalClause
      (D := mkFullyConcreteNavierStokesSurface)
      (P := { viscosity := ν
              viscosity_pos := hν
              initialVelocity := (0 : NSInitialVelocity)
              smooth_initial := smoothInitialVelocityData_zero
              divergence_free_initial := by
                intro x
                simpa using (initialSpatialDivergence_zero x) })
      nsCoord0).2
      (zeroNavierStokesGlobalRegularityWitness_nonempty hν)

theorem component_shadow_without_sharedWitness_clause_regression
    {ν : ℝ} (hν : 0 < ν) :
    FeffermanGlobalRegularityClause
        (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
          (constantInitialVelocityProblemData ν hν splitSharedWitnessCounterexampleVelocity)
          nsCoord0) ∧
      ¬ SharedWitnessComponentRegularityClause
          mkFullyConcreteNavierStokesSurface
          (constantInitialVelocityProblemData ν hν splitSharedWitnessCounterexampleVelocity)
          nsCoord0 := by
  exact
    componentFeffermanClause_without_sharedWitnessComponentClause_constantInitialVelocity
      (ν := ν) hν splitSharedWitnessCounterexampleVelocity_ne_zero
      splitSharedWitnessCounterexampleVelocity_component_zero

end NavierStokesSharedWitnessComponentRegression

end NavierStokes
end FluidDynamics
end Mettapedia
