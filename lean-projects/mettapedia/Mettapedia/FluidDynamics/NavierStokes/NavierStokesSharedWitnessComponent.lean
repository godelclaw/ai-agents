import Mettapedia.FluidDynamics.NavierStokes.NavierStokesComponentShadowIncoherence

/-!
# Shared-Witness Component Clause on the Concrete Navier-Stokes Surface

The current scalar `toComponentPredicateKit` allows each output-side slot to use
its own existential vector lift.  This file isolates the stronger notion that
the route would actually need in order to talk about one coherent vector-valued
Navier-Stokes witness behind a scalar component.

That stronger component clause is equivalent to the full vector-valued
`NavierStokesGlobalRegularityClause`: it is just the same witness, viewed
through one chosen coordinate.  Therefore any scalar route that wants to
recover the concrete theorem has to supply an implication from the current
component shadow to this shared-witness clause.  The constant-data countermodel
from `NavierStokesComponentShadowIncoherence` shows that the present shadow
does not do so.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SharedWitnessComponent

/-- A scalar component output backed by one shared concrete vector-valued NS
witness.  Unlike `toComponentPredicateKit`, all slots are tied to the same
underlying witness. -/
structure SharedWitnessComponentRegularityOutput
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) (i : Fin 3) where
  witness : NavierStokesGlobalRegularityWitness D P
  velocity : NSScalarField
  component_eq : velocityComponent witness.velocity i = velocity

/-- Prop-level wrapper for the existence of a shared-witness component output. -/
def SharedWitnessComponentRegularityClause
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) (i : Fin 3) : Prop :=
  Nonempty (SharedWitnessComponentRegularityOutput D P i)

/-- Any full vector-valued witness induces a shared-witness scalar component
output. -/
def NavierStokesGlobalRegularityWitness.toSharedWitnessComponentOutput
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (W : NavierStokesGlobalRegularityWitness D P) (i : Fin 3) :
    SharedWitnessComponentRegularityOutput D P i where
  witness := W
  velocity := velocityComponent W.velocity i
  component_eq := rfl

/-- A shared-witness component output immediately realizes the current scalar
component-shadow clause. -/
def SharedWitnessComponentRegularityOutput.toComponentFeffermanOutput
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D} {i : Fin 3}
    (B : SharedWitnessComponentRegularityOutput D P i) :
    FeffermanGlobalRegularityOutput (D.toComponentPredicateKit P i) where
  velocity := B.velocity
  pressure := B.witness.pressure
  smooth_velocity := ⟨B.witness.velocity, B.witness.smooth_velocity, B.component_eq⟩
  smooth_pressure := B.witness.smooth_pressure
  momentum_equation := ⟨B.witness.velocity, B.witness.smooth_velocity,
    B.component_eq, B.witness.momentum_equation⟩
  incompressible := ⟨B.witness.velocity, B.witness.incompressible, B.component_eq⟩
  initial_condition := ⟨B.witness.velocity, B.witness.initial_condition, B.component_eq⟩
  bounded_energy := ⟨B.witness.velocity, B.witness.bounded_energy, B.component_eq⟩

/-- Therefore a shared-witness component clause implies the current scalar
component-shadow clause. -/
theorem SharedWitnessComponentRegularityClause.implies_componentFeffermanClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D} {i : Fin 3}
    (h : SharedWitnessComponentRegularityClause D P i) :
    FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  rcases h with ⟨B⟩
  exact ⟨B.toComponentFeffermanOutput⟩

/-- Any full vector-valued clause implies the shared-witness component clause. -/
theorem NavierStokesGlobalRegularityClause.implies_sharedWitnessComponentClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (h : NavierStokesGlobalRegularityClause D P) (i : Fin 3) :
    SharedWitnessComponentRegularityClause D P i := by
  rcases h with ⟨W⟩
  exact ⟨W.toSharedWitnessComponentOutput i⟩

/-- Conversely, a shared-witness component clause already contains a full
vector-valued witness. -/
theorem SharedWitnessComponentRegularityClause.implies_globalClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D} {i : Fin 3}
    (h : SharedWitnessComponentRegularityClause D P i) :
    NavierStokesGlobalRegularityClause D P := by
  rcases h with ⟨B⟩
  exact ⟨B.witness⟩

/-- So the shared-witness component clause is exactly equivalent to the full
vector-valued clause. -/
theorem sharedWitnessComponentRegularityClause_iff_globalClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D} (i : Fin 3) :
    SharedWitnessComponentRegularityClause D P i ↔
      NavierStokesGlobalRegularityClause D P := by
  constructor
  · exact SharedWitnessComponentRegularityClause.implies_globalClause
  · intro h
    exact h.implies_sharedWitnessComponentClause i

/-- The current component shadow is still too weak to imply a shared vector
witness: on nonzero constant initial data with one vanishing coordinate, the
scalar component clause holds while the shared-witness clause fails. -/
theorem componentFeffermanClause_without_sharedWitnessComponentClause_constantInitialVelocity
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} {i : Fin 3}
    (hc : c ≠ 0)
    (hci : c i = 0) :
    FeffermanGlobalRegularityClause
        (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
          (constantInitialVelocityProblemData ν hν c) i) ∧
      ¬ SharedWitnessComponentRegularityClause
          mkFullyConcreteNavierStokesSurface
          (constantInitialVelocityProblemData ν hν c) i := by
  constructor
  · exact componentFeffermanClause_constantInitialVelocity_of_component_eq_zero hν hci
  · intro hshared
    have hglobal :
        NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          (constantInitialVelocityProblemData ν hν c) := by
      exact
        (sharedWitnessComponentRegularityClause_iff_globalClause (D := mkFullyConcreteNavierStokesSurface)
          (P := constantInitialVelocityProblemData ν hν c) i).mp hshared
    exact
      (componentFeffermanClause_without_concreteClause_constantInitialVelocity
        (ν := ν) hν hc hci).2 hglobal

end SharedWitnessComponent

end NavierStokes
end FluidDynamics
end Mettapedia
