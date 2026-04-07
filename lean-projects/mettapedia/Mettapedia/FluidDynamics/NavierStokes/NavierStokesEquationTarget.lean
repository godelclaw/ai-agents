import Mettapedia.FluidDynamics.NavierStokes.FeffermanTargetBack
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Concrete Navier-Stokes Equation Target

This file adds the first literal Navier--Stokes theorem surface to the current
NS lane.  It fixes the ambient domain to time `ℝ` and space `ℝ^3`, introduces
named differential operators for the momentum equation and incompressibility,
packages smooth/divergence-free initial data, and then records the honest
connection back to the existing scalar Fefferman-style bridge surface.

The operators are still supplied abstractly, but the equation being targeted is
no longer hidden behind arbitrary predicates:

`∂ₜ u + (u · ∇)u + ∇p = ν Δu`, `div u = 0`, `u(0, ·) = u₀`.

The current grassroots bridge is scalar-valued, so this file only maps a full
vector-valued NS witness down to a scalar component shadow.  It does not claim
that the present scalar bridge already proves the full vector theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

/-- Spatial domain for the local NS target: `ℝ^3`. -/
abbrev NSSpace := EuclideanSpace ℝ (Fin 3)

/-- Time parameter for the local NS target. -/
abbrev NSTime := ℝ

/-- Vector-valued velocity fields on `ℝ × ℝ^3`. -/
abbrev NSVelocityField := NSTime → NSSpace → NSSpace

/-- Scalar-valued space-time fields on `ℝ × ℝ^3`. -/
abbrev NSScalarField := NSTime → NSSpace → ℝ

/-- Pressure fields on `ℝ × ℝ^3`. -/
abbrev NSPressureField := NSScalarField

/-- Initial velocity data on `ℝ^3`. -/
abbrev NSInitialVelocity := NSSpace → NSSpace

/-- Spatial Fréchet derivative of a velocity field at fixed time. -/
def spatialFDeriv (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    NSSpace →L[ℝ] NSSpace :=
  fderiv ℝ (fun y : NSSpace => u t y) x

/-- Spatial divergence on `ℝ^3`, defined as the trace of the spatial Fréchet
derivative against the standard Euclidean basis. -/
def spatialDivergence (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ∑ i : Fin 3, (spatialFDeriv u t x (EuclideanSpace.single i (1 : ℝ))) i

/-- Divergence of the initial velocity data on `ℝ^3`. -/
def initialSpatialDivergence (u₀ : NSInitialVelocity) (x : NSSpace) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ u₀ x (EuclideanSpace.single i (1 : ℝ))) i

/-- Time Fréchet derivative of a velocity field at fixed spatial point. -/
def timeFDeriv (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ℝ →L[ℝ] NSSpace :=
  fderiv ℝ (fun s : NSTime => u s x) t

/-- Time derivative `∂ₜ u` on `ℝ × ℝ^3`, defined by applying the time Fréchet
derivative to the unit time direction. -/
def timeVelocityDerivative (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  timeFDeriv u t x (1 : ℝ)

/-- Convection term `(u · ∇)u` on `ℝ × ℝ^3`, defined by applying the spatial
Fréchet derivative to the current velocity vector. -/
def spatialConvection (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialFDeriv u t x (u t x)

/-- Spatial pressure gradient on `ℝ^3`, defined by the actual gradient of the
scalar pressure field at fixed time. -/
def spatialPressureGradient (p : NSPressureField) (t : NSTime) (x : NSSpace) : NSSpace :=
  gradient (fun y : NSSpace => p t y) x

/-- Differential-operator kit for a concrete NS theorem statement.  The hard
analytic work still lives in these operators and regularity predicates, but the
equation itself is now explicit. -/
structure NavierStokesDifferentialKit where
  timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace
  convection : NSVelocityField → NSTime → NSSpace → NSSpace
  pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace
  laplacian : NSVelocityField → NSTime → NSSpace → NSSpace
  divergence : NSVelocityField → NSTime → NSSpace → ℝ
  smoothVelocity : NSVelocityField → Prop
  smoothPressure : NSPressureField → Prop
  boundedEnergy : NSVelocityField → Prop
  smoothInitialData : NSInitialVelocity → Prop
  divergenceFreeInitialData : NSInitialVelocity → Prop

/-- A partially concrete NS differential kit where divergence and divergence-free
initial data are no longer abstract: they are given by the actual trace of the
spatial Fréchet derivative on `ℝ^3`. -/
def mkWithConcreteDivergence
    (timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace)
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeDerivative
  convection := convection
  pressureGradient := pressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A further partially concrete NS differential kit where both pressure
gradient and divergence are fixed to their actual calculus-side meanings on
`ℝ^3`. -/
def mkWithConcreteGradientAndDivergence
    (timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace)
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeDerivative
  convection := convection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A still more concrete NS differential kit where time derivative, pressure
gradient, divergence, and divergence-free initial data are all fixed to their
actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteTimeGradientAndDivergence
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := convection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A yet more concrete NS differential kit where time derivative, convection,
pressure gradient, divergence, and divergence-free initial data are all fixed
to their actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteTimeConvectionGradientAndDivergence
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- Smooth divergence-free initial data together with a positive viscosity. -/
structure NavierStokesProblemData (D : NavierStokesDifferentialKit) where
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  initialVelocity : NSInitialVelocity
  smooth_initial : D.smoothInitialData initialVelocity
  divergence_free_initial : D.divergenceFreeInitialData initialVelocity

/-- Pointwise momentum equation `∂ₜ u + (u · ∇)u + ∇p = ν Δu`. -/
def SatisfiesMomentumEquation
    (D : NavierStokesDifferentialKit) (ν : ℝ)
    (u : NSVelocityField) (p : NSPressureField) : Prop :=
  ∀ t x,
    D.timeDerivative u t x + D.convection u t x + D.pressureGradient p t x =
      ν • D.laplacian u t x

/-- Pointwise incompressibility `div u = 0`. -/
def IsIncompressible
    (D : NavierStokesDifferentialKit) (u : NSVelocityField) : Prop :=
  ∀ t x, D.divergence u t x = 0

/-- Initial condition `u(0, ·) = u₀`. -/
def MatchesInitialVelocity
    (u₀ : NSInitialVelocity) (u : NSVelocityField) : Prop :=
  ∀ x, u 0 x = u₀ x

/-- Concrete global-regularity witness for the local NS target. -/
structure NavierStokesGlobalRegularityWitness
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) where
  velocity : NSVelocityField
  pressure : NSPressureField
  smooth_velocity : D.smoothVelocity velocity
  smooth_pressure : D.smoothPressure pressure
  momentum_equation :
    SatisfiesMomentumEquation D P.viscosity velocity pressure
  incompressible : IsIncompressible D velocity
  initial_condition : MatchesInitialVelocity P.initialVelocity velocity
  bounded_energy : D.boundedEnergy velocity

/-- Concrete existence clause for the local NS target. -/
def NavierStokesGlobalRegularityClause
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) : Prop :=
  Nonempty (NavierStokesGlobalRegularityWitness D P)

/-- First local theorem target mirroring the shape of the Clay/Fefferman
problem: every admissible initial datum admits a global regularity witness. -/
def NavierStokesMillenniumTarget
    (D : NavierStokesDifferentialKit) : Prop :=
  ∀ P : NavierStokesProblemData D, NavierStokesGlobalRegularityClause D P

/-- Scalar component of a vector-valued velocity field. -/
def velocityComponent (u : NSVelocityField) (i : Fin 3) : NSScalarField :=
  fun t x => u t x i

/-- Componentwise scalar shadow of the concrete vector-valued NS target.  This
is the honest meeting point with the current scalar Fefferman bridge surface. -/
def NavierStokesDifferentialKit.toComponentPredicateKit
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) (i : Fin 3) :
    FeffermanPredicateKit (Time := NSTime) (X := NSSpace) where
  SmoothVelocity := fun u =>
    ∃ U : NSVelocityField, D.smoothVelocity U ∧ velocityComponent U i = u
  SmoothPressure := D.smoothPressure
  MomentumEquation := fun u p =>
    ∃ U : NSVelocityField,
      D.smoothVelocity U ∧
      velocityComponent U i = u ∧
      SatisfiesMomentumEquation D P.viscosity U p
  Incompressible := fun u =>
    ∃ U : NSVelocityField, IsIncompressible D U ∧ velocityComponent U i = u
  InitialCondition := fun u =>
    ∃ U : NSVelocityField,
      MatchesInitialVelocity P.initialVelocity U ∧ velocityComponent U i = u
  BoundedEnergy := fun u =>
    ∃ U : NSVelocityField, D.boundedEnergy U ∧ velocityComponent U i = u

/-- Any full NS witness yields a scalar component witness for the current
Fefferman-style output shell. -/
def NavierStokesGlobalRegularityWitness.toComponentFeffermanOutput
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (W : NavierStokesGlobalRegularityWitness D P) (i : Fin 3) :
    FeffermanGlobalRegularityOutput (D.toComponentPredicateKit P i) where
  velocity := velocityComponent W.velocity i
  pressure := W.pressure
  smooth_velocity := ⟨W.velocity, W.smooth_velocity, rfl⟩
  smooth_pressure := W.smooth_pressure
  momentum_equation := ⟨W.velocity, W.smooth_velocity, rfl, W.momentum_equation⟩
  incompressible := ⟨W.velocity, W.incompressible, rfl⟩
  initial_condition := ⟨W.velocity, W.initial_condition, rfl⟩
  bounded_energy := ⟨W.velocity, W.bounded_energy, rfl⟩

/-- Therefore a full vector-valued NS clause implies the scalar component shadow
seen by the current route. -/
theorem NavierStokesGlobalRegularityClause.implies_componentFeffermanClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (h : NavierStokesGlobalRegularityClause D P) (i : Fin 3) :
    FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  rcases h with ⟨W⟩
  exact ⟨W.toComponentFeffermanOutput i⟩

/-- Likewise, a full theorem target immediately implies the component-level
Fefferman-style target for every coordinate. -/
theorem NavierStokesMillenniumTarget.implies_componentFeffermanTarget
    {D : NavierStokesDifferentialKit}
    (h : NavierStokesMillenniumTarget D) (i : Fin 3) :
    ∀ P : NavierStokesProblemData D,
      FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  intro P
  exact (NavierStokesGlobalRegularityClause.implies_componentFeffermanClause
    (D := D) (P := P) (h P) i)

/-- For the partially concrete kit, incompressibility is literally the vanishing
of the spatial divergence defined above. -/
theorem isIncompressible_mkWithConcreteDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDivergence timeDerivative convection pressureGradient laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Likewise, divergence-free initial data are now literally the vanishing of
the spatial initial divergence. -/
theorem divergenceFreeInitialData_mkWithConcreteDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDivergence timeDerivative convection pressureGradient laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- For the more concrete kit, the momentum equation literally uses the actual
spatial pressure gradient on `ℝ^3`. -/
theorem satisfiesMomentumEquation_mkWithConcreteGradientAndDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteGradientAndDivergence timeDerivative convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeDerivative u t x + convection u t x + spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same concrete kit, incompressibility is again the vanishing of the
explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteGradientAndDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteGradientAndDivergence timeDerivative convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- For the most concrete current kit, the momentum equation literally uses the
actual time derivative, spatial pressure gradient, and the chosen convection
and Laplacian operators. -/
theorem satisfiesMomentumEquation_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteTimeGradientAndDivergence convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + convection u t x + spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same fully concrete current kit, incompressibility is the vanishing
of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteTimeGradientAndDivergence convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same fully concrete current kit. -/
theorem divergenceFreeInitialData_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteTimeGradientAndDivergence convection laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- In the currently most concrete kit, the momentum equation literally uses
the actual time derivative, convection term, and pressure gradient on
`ℝ × ℝ^3`. -/
theorem satisfiesMomentumEquation_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same most concrete current kit, incompressibility is still exactly
the vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same most concrete current kit. -/
theorem divergenceFreeInitialData_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
