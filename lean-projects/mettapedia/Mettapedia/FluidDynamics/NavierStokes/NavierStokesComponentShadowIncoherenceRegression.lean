import Mettapedia.FluidDynamics.NavierStokes.NavierStokesComponentShadowIncoherence

/-!
# Regression tests for component-shadow incoherence
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace NavierStokesComponentShadowIncoherenceRegression

/-- A concrete nonzero constant velocity whose first component vanishes. -/
def splitShadowCounterexampleVelocity : NSSpace :=
  EuclideanSpace.single nsCoord1 (1 : ℝ)

theorem splitShadowCounterexampleVelocity_ne_zero :
    splitShadowCounterexampleVelocity ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord1) h
  simp [splitShadowCounterexampleVelocity] at h1

theorem splitShadowCounterexampleVelocity_component_zero :
    splitShadowCounterexampleVelocity nsCoord0 = 0 := by
  have hne : nsCoord0 ≠ nsCoord1 := by decide
  simp [splitShadowCounterexampleVelocity, hne]

theorem component_shadow_constant_initial_velocity_regression
    {ν : ℝ} (hν : 0 < ν) :
    FeffermanGlobalRegularityClause
      (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
        (constantInitialVelocityProblemData ν hν splitShadowCounterexampleVelocity)
        nsCoord0) := by
  exact
    componentFeffermanClause_constantInitialVelocity_of_component_eq_zero
      (ν := ν) hν splitShadowCounterexampleVelocity_component_zero

theorem component_shadow_zero_output_regression
    {ν : ℝ} (hν : 0 < ν) :
    (componentShadowZeroOutput
      (constantInitialVelocityProblemData ν hν splitShadowCounterexampleVelocity)
      nsCoord0
      (by
        intro x
        simpa [constantInitialVelocity] using splitShadowCounterexampleVelocity_component_zero)).velocity = 0 := by
  simp

theorem component_shadow_without_concrete_clause_regression
    {ν : ℝ} (hν : 0 < ν) :
    FeffermanGlobalRegularityClause
        (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
          (constantInitialVelocityProblemData ν hν splitShadowCounterexampleVelocity)
          nsCoord0) ∧
      ¬ NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          (constantInitialVelocityProblemData ν hν splitShadowCounterexampleVelocity) := by
  exact
    componentFeffermanClause_without_concreteClause_constantInitialVelocity
      (ν := ν) hν splitShadowCounterexampleVelocity_ne_zero
      splitShadowCounterexampleVelocity_component_zero

theorem no_component_shadow_to_concrete_bridge_regression :
    ¬ (∀ (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface) (i : Fin 3),
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) →
          NavierStokesGlobalRegularityClause mkFullyConcreteNavierStokesSurface P) := by
  exact not_componentFeffermanClause_implies_concreteNavierStokesGlobalRegularityClause

end NavierStokesComponentShadowIncoherenceRegression

end NavierStokes
end FluidDynamics
end Mettapedia
