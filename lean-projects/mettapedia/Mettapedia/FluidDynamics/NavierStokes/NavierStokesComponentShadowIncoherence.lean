import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Component Shadow Incoherence on the Concrete Navier-Stokes Surface

The current scalar `toComponentPredicateKit` weakens the concrete vector-valued
Navier-Stokes target in a precise way: each target-side slot is allowed to use
its own existential vector lift.  This file records that weakness explicitly.

If one component of the initial datum vanishes, the component shadow clause is
already inhabited by the zero scalar field, even though the initial-condition
slot is witnessed by a different time-independent vector field.  Specializing
to nonzero constant initial data with one zero component yields a direct gap:
the scalar component clause is true while the full concrete vector clause is
false.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ComponentShadow

/-- A zero scalar component output on the current component-shadow surface.

The smoothness, PDE, incompressibility, and bounded-energy slots are witnessed
by the zero vector field.  The initial-condition slot is witnessed separately by
the time-independent seed attached to the full initial datum.  So this is an
explicit witness to the split existential nature of `toComponentPredicateKit`.
-/
def componentShadowZeroOutput
    (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface)
    (i : Fin 3)
    (hzero : ∀ x, P.initialVelocity x i = 0) :
    FeffermanGlobalRegularityOutput
      (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) where
  velocity := 0
  pressure := 0
  smooth_velocity := by
    let W0 := zeroNavierStokesGlobalRegularityWitness P.viscosity_pos
    exact ⟨(0 : NSVelocityField), W0.smooth_velocity, by
      funext t x
      rfl⟩
  smooth_pressure := by
    let W0 := zeroNavierStokesGlobalRegularityWitness P.viscosity_pos
    simpa using W0.smooth_pressure
  momentum_equation := by
    let W0 := zeroNavierStokesGlobalRegularityWitness P.viscosity_pos
    exact ⟨(0 : NSVelocityField), W0.smooth_velocity, by
      funext t x
      rfl, W0.momentum_equation⟩
  incompressible := by
    let W0 := zeroNavierStokesGlobalRegularityWitness P.viscosity_pos
    exact ⟨(0 : NSVelocityField), W0.incompressible, by
      funext t x
      rfl⟩
  initial_condition := by
    refine ⟨timeIndependentVelocity P.initialVelocity,
      MatchesInitialVelocity_timeIndependentVelocity P.initialVelocity, ?_⟩
    funext t x
    simpa [velocityComponent, timeIndependentVelocity] using hzero x
  bounded_energy := by
    let W0 := zeroNavierStokesGlobalRegularityWitness P.viscosity_pos
    exact ⟨(0 : NSVelocityField), W0.bounded_energy, by
      funext t x
      rfl⟩

@[simp] theorem componentShadowZeroOutput_velocity
    (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface)
    (i : Fin 3)
    (hzero : ∀ x, P.initialVelocity x i = 0) :
    (componentShadowZeroOutput P i hzero).velocity = 0 :=
  rfl

@[simp] theorem componentShadowZeroOutput_pressure
    (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface)
    (i : Fin 3)
    (hzero : ∀ x, P.initialVelocity x i = 0) :
    (componentShadowZeroOutput P i hzero).pressure = 0 :=
  rfl

/-- If one component of the initial datum vanishes identically, the current
component-shadow clause is already inhabited by the zero scalar field. -/
theorem componentFeffermanClause_of_component_zero_initialVelocity
    (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface)
    (i : Fin 3)
    (hzero : ∀ x, P.initialVelocity x i = 0) :
    FeffermanGlobalRegularityClause
      (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) :=
  ⟨componentShadowZeroOutput P i hzero⟩

/-- Constant initial data packaged as concrete fully differential problem data. -/
def constantInitialVelocityProblemData
    (ν : ℝ) (hν : 0 < ν) (c : NSSpace) :
    NavierStokesProblemData mkFullyConcreteNavierStokesSurface where
  viscosity := ν
  viscosity_pos := hν
  initialVelocity := constantInitialVelocity c
  smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
  divergence_free_initial := by
    intro x
    simpa using initialSpatialDivergence_constantInitialVelocity c x

/-- On nonzero constant initial data, any vanishing coordinate already gives an
inhabited scalar component clause on the current shadow surface. -/
theorem componentFeffermanClause_constantInitialVelocity_of_component_eq_zero
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} {i : Fin 3}
    (hci : c i = 0) :
    FeffermanGlobalRegularityClause
      (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
        (constantInitialVelocityProblemData ν hν c) i) := by
  exact
    componentFeffermanClause_of_component_zero_initialVelocity
      (P := constantInitialVelocityProblemData ν hν c) i
      (by
        intro x
        simpa [constantInitialVelocity] using hci)

/-- Therefore the current scalar component shadow is strictly weaker than the
actual concrete vector-valued clause: for nonzero constant data with one zero
component, the scalar clause is inhabited while the concrete clause is false. -/
theorem componentFeffermanClause_without_concreteClause_constantInitialVelocity
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} {i : Fin 3}
    (hc : c ≠ 0)
    (hci : c i = 0) :
    FeffermanGlobalRegularityClause
        (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
          (constantInitialVelocityProblemData ν hν c) i) ∧
      ¬ NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          (constantInitialVelocityProblemData ν hν c) := by
  constructor
  · exact componentFeffermanClause_constantInitialVelocity_of_component_eq_zero hν hci
  · simpa [constantInitialVelocityProblemData] using
      (not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity
        (ν := ν) (c := c) hν hc)

/-- A single scalar component shadow cannot be used as a universal bridge back
to the concrete vector-valued Navier-Stokes clause.

The counterexample is nonzero constant initial data in the `x₁` direction,
viewed through the zero `x₀` component.  The scalar component clause is
inhabited by `componentShadowZeroOutput`, while the full concrete clause is
blocked by the whole-space bounded-energy obstruction for nonzero constants. -/
theorem not_componentFeffermanClause_implies_concreteNavierStokesGlobalRegularityClause :
    ¬ (∀ (P : NavierStokesProblemData mkFullyConcreteNavierStokesSurface) (i : Fin 3),
        FeffermanGlobalRegularityClause
            (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit P i) →
          NavierStokesGlobalRegularityClause mkFullyConcreteNavierStokesSurface P) := by
  intro hbridge
  let c : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  have hc : c ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hzero
    simp [c] at hcoord
  have hci : c nsCoord0 = 0 := by
    have hne : nsCoord0 ≠ nsCoord1 := by decide
    simp [c, hne]
  have hsplit :
      FeffermanGlobalRegularityClause
          (mkFullyConcreteNavierStokesSurface.toComponentPredicateKit
            (constantInitialVelocityProblemData (1 : ℝ) zero_lt_one c)
            nsCoord0) ∧
        ¬ NavierStokesGlobalRegularityClause
            mkFullyConcreteNavierStokesSurface
            (constantInitialVelocityProblemData (1 : ℝ) zero_lt_one c) := by
    exact
      componentFeffermanClause_without_concreteClause_constantInitialVelocity
        (ν := (1 : ℝ)) zero_lt_one hc hci
  exact hsplit.2
    (hbridge
      (constantInitialVelocityProblemData (1 : ℝ) zero_lt_one c)
      nsCoord0 hsplit.1)

end ComponentShadow

end NavierStokes
end FluidDynamics
end Mettapedia
