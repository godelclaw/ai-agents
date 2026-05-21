import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSharedWitnessComponent

/-!
# No Uniform Bridge from the Current Component Shadow to a Shared Witness

`NavierStokesSharedWitnessComponent.lean` shows that for a fixed datum, the
current scalar component shadow need not imply even the weakest coherent repair
where one shared vector-valued NS witness supports the chosen component.

This file packages the stronger route-level consequence: there is no datum-uniform
bridge theorem of that form, even when one fixes the coordinate in advance.
For each coordinate `i`, a nonzero constant velocity pointing in a different
coordinate gives a datum where the current component shadow holds but the
shared-witness component clause fails.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SharedWitnessBridgeObstruction

/-- Nonzero constant datum used to obstruct a uniform bridge for the first
coordinate. -/
def sharedWitnessBridgeCounterexampleVelocity0 : NSSpace :=
  EuclideanSpace.single nsCoord1 (1 : ℝ)

/-- Nonzero constant datum used to obstruct a uniform bridge for the second
coordinate. -/
def sharedWitnessBridgeCounterexampleVelocity1 : NSSpace :=
  EuclideanSpace.single nsCoord2 (1 : ℝ)

/-- Nonzero constant datum used to obstruct a uniform bridge for the third
coordinate. -/
def sharedWitnessBridgeCounterexampleVelocity2 : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem sharedWitnessBridgeCounterexampleVelocity0_ne_zero :
    sharedWitnessBridgeCounterexampleVelocity0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord1) h
  simp [sharedWitnessBridgeCounterexampleVelocity0] at h1

theorem sharedWitnessBridgeCounterexampleVelocity1_ne_zero :
    sharedWitnessBridgeCounterexampleVelocity1 ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord2) h
  simp [sharedWitnessBridgeCounterexampleVelocity1] at h1

theorem sharedWitnessBridgeCounterexampleVelocity2_ne_zero :
    sharedWitnessBridgeCounterexampleVelocity2 ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NSSpace => v nsCoord0) h
  simp [sharedWitnessBridgeCounterexampleVelocity2] at h1

theorem sharedWitnessBridgeCounterexampleVelocity0_component_zero :
    sharedWitnessBridgeCounterexampleVelocity0 nsCoord0 = 0 := by
  have hne : nsCoord0 ≠ nsCoord1 := by decide
  simp [sharedWitnessBridgeCounterexampleVelocity0, hne]

theorem sharedWitnessBridgeCounterexampleVelocity1_component_zero :
    sharedWitnessBridgeCounterexampleVelocity1 nsCoord1 = 0 := by
  have hne : nsCoord1 ≠ nsCoord2 := by decide
  simp [sharedWitnessBridgeCounterexampleVelocity1, hne]

theorem sharedWitnessBridgeCounterexampleVelocity2_component_zero :
    sharedWitnessBridgeCounterexampleVelocity2 nsCoord2 = 0 := by
  have hne : nsCoord2 ≠ nsCoord0 := by decide
  simp [sharedWitnessBridgeCounterexampleVelocity2, hne]

/-- There is no datum-uniform bridge from the current first-coordinate scalar
shadow to the coherent shared-witness component clause. -/
theorem not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord0 :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord0) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord0 := by
  intro hbridge
  let P :=
    constantInitialVelocityProblemData 1 zero_lt_one sharedWitnessBridgeCounterexampleVelocity0
  have hpair :=
    componentFeffermanClause_without_sharedWitnessComponentClause_constantInitialVelocity
      (ν := 1) zero_lt_one sharedWitnessBridgeCounterexampleVelocity0_ne_zero
      sharedWitnessBridgeCounterexampleVelocity0_component_zero
  exact hpair.2 (hbridge P hpair.1)

/-- There is no datum-uniform bridge from the current second-coordinate scalar
shadow to the coherent shared-witness component clause. -/
theorem not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord1 :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord1) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord1 := by
  intro hbridge
  let P :=
    constantInitialVelocityProblemData 1 zero_lt_one sharedWitnessBridgeCounterexampleVelocity1
  have hpair :=
    componentFeffermanClause_without_sharedWitnessComponentClause_constantInitialVelocity
      (ν := 1) zero_lt_one sharedWitnessBridgeCounterexampleVelocity1_ne_zero
      sharedWitnessBridgeCounterexampleVelocity1_component_zero
  exact hpair.2 (hbridge P hpair.1)

/-- There is no datum-uniform bridge from the current third-coordinate scalar
shadow to the coherent shared-witness component clause. -/
theorem not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord2 :
    ¬ ∀ P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface,
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P nsCoord2) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P nsCoord2 := by
  intro hbridge
  let P :=
    constantInitialVelocityProblemData 1 zero_lt_one sharedWitnessBridgeCounterexampleVelocity2
  have hpair :=
    componentFeffermanClause_without_sharedWitnessComponentClause_constantInitialVelocity
      (ν := 1) zero_lt_one sharedWitnessBridgeCounterexampleVelocity2_ne_zero
      sharedWitnessBridgeCounterexampleVelocity2_component_zero
  exact hpair.2 (hbridge P hpair.1)

/-- In particular there is no coordinate-uniform theorem that upgrades the
current scalar component shadow to the coherent shared-witness clause. -/
theorem not_uniform_componentShadowBridge_to_sharedWitnessComponent :
    ¬ ∀ (i : Fin 3) (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface),
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) →
          SharedWitnessComponentRegularityClause
            mkFullyConcreteNavierStokesSurface P i := by
  intro hbridge
  exact
    not_uniform_componentShadowBridge_to_sharedWitnessComponent_nsCoord0
      (fun P hP => hbridge nsCoord0 P hP)

end SharedWitnessBridgeObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
