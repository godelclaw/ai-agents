import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSharedWitnessBridgeObstruction

/-!
# Regression tests for the shared-witness bridge obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace NavierStokesSharedWitnessBridgeObstructionRegression

theorem sharedWitnessBridgeCounterexampleVelocity0_component_zero_regression :
    sharedWitnessBridgeCounterexampleVelocity0 nsCoord0 = 0 :=
  sharedWitnessBridgeCounterexampleVelocity0_component_zero

theorem sharedWitnessBridgeCounterexampleVelocity1_component_zero_regression :
    sharedWitnessBridgeCounterexampleVelocity1 nsCoord1 = 0 :=
  sharedWitnessBridgeCounterexampleVelocity1_component_zero

theorem sharedWitnessBridgeCounterexampleVelocity2_component_zero_regression :
    sharedWitnessBridgeCounterexampleVelocity2 nsCoord2 = 0 :=
  sharedWitnessBridgeCounterexampleVelocity2_component_zero

theorem no_uniform_bridge_nsCoord0_regression :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord0) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord0 :=
  not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord0

theorem no_uniform_bridge_nsCoord1_regression :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord1) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord1 :=
  not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord1

theorem no_uniform_bridge_nsCoord2_regression :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord2) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord2 :=
  not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord2

theorem no_uniform_bridge_any_coordinate_regression :
    ¬ ∀ (i : Fin 3) (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface),
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P i :=
  not_uniform_componentShadowBridge_to_sharedWitnessComponent

end NavierStokesSharedWitnessBridgeObstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
