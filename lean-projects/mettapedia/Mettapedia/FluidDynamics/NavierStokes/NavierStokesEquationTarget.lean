import Mettapedia.FluidDynamics.NavierStokes.FeffermanTargetBack
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

open scoped Laplacian ContDiff

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

/-- Space-time domain `ℝ × ℝ^3` for the concrete NS theorem surface. -/
abbrev NSSpacetime := NSTime × NSSpace

/-- Uncurried space-time form of a velocity field. -/
def spaceTimeVelocityMap (u : NSVelocityField) : NSSpacetime → NSSpace :=
  fun tx => u tx.1 tx.2

/-- Uncurried space-time form of a pressure field. -/
def spaceTimePressureMap (p : NSPressureField) : NSSpacetime → ℝ :=
  fun tx => p tx.1 tx.2

/-- Concrete `C^∞` smoothness predicate for velocity fields on `ℝ × ℝ^3`. -/
def smoothSpaceTimeVelocity (u : NSVelocityField) : Prop :=
  ContDiff ℝ ∞ (spaceTimeVelocityMap u)

/-- Concrete `C^∞` smoothness predicate for pressure fields on `ℝ × ℝ^3`. -/
def smoothSpaceTimePressure (p : NSPressureField) : Prop :=
  ContDiff ℝ ∞ (spaceTimePressureMap p)

/-- Concrete `C^∞` smoothness predicate for initial velocity data on `ℝ^3`. -/
def smoothInitialVelocityData (u₀ : NSInitialVelocity) : Prop :=
  ContDiff ℝ ∞ u₀

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

/-- Spatial Laplacian on `ℝ^3`, defined by the actual Laplacian of the fixed-time
velocity slice. -/
def spatialLaplacian (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  Δ (fun y : NSSpace => u t y) x

/-- Pointwise kinetic-energy density `|u(t,x)|^2` on `ℝ^3`. -/
def kineticEnergyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ‖u t x‖ ^ (2 : ℕ)

/-- Spatial kinetic energy of a velocity slice, measured against Lebesgue volume
on `ℝ^3`. -/
def kineticEnergyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, kineticEnergyDensity u t x ∂(MeasureTheory.volume : MeasureTheory.Measure NSSpace)

/-- Pointwise initial kinetic-energy density `|u₀(x)|^2` on `ℝ^3`. -/
def initialKineticEnergyDensity (u₀ : NSInitialVelocity) : NSSpace → ℝ :=
  fun x => ‖u₀ x‖ ^ (2 : ℕ)

/-- Finite-energy admissibility for concrete initial data on `ℝ^3`. -/
def finiteInitialKineticEnergy (u₀ : NSInitialVelocity) : Prop :=
  MeasureTheory.Integrable (initialKineticEnergyDensity u₀)

/-- Concrete bounded-energy predicate: the kinetic energy is integrable on every
time slice and uniformly bounded in time. -/
def boundedKineticEnergy (u : NSVelocityField) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
    MeasureTheory.Integrable (kineticEnergyDensity u t) ∧ kineticEnergyAt u t ≤ C

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

/-- A fully differential-side concrete NS kit where time derivative, convection,
pressure gradient, Laplacian, divergence, and divergence-free initial data are
all fixed to their actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteDifferentialOperators
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A theorem surface where the full differential operator content and the
smoothness predicates are all concrete; only bounded energy remains abstract. -/
def mkWithConcreteDifferentialOperatorsAndSmoothness
    (boundedEnergy : NSVelocityField → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothSpaceTimeVelocity
  smoothPressure := smoothSpaceTimePressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialVelocityData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A fully concrete theorem surface where the differential operators,
smoothness predicates, and bounded-energy predicate are all literal. -/
def mkFullyConcreteNavierStokesSurface :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothSpaceTimeVelocity
  smoothPressure := smoothSpaceTimePressure
  boundedEnergy := boundedKineticEnergy
  smoothInitialData := smoothInitialVelocityData
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

/-- Fully concrete local theorem target: smooth divergence-free initial data on
`ℝ^3` with positive viscosity admit a global smooth incompressible solution with
bounded kinetic energy on `ℝ × ℝ^3`. -/
def ConcreteNavierStokesMillenniumTarget : Prop :=
  NavierStokesMillenniumTarget mkFullyConcreteNavierStokesSurface

/-- Fully explicit concrete global-regularity clause for fixed viscosity and
initial data on `ℝ^3`. -/
def ExplicitConcreteNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
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

/-- Fully explicit local whole-space surrogate theorem target: every smooth
divergence-free initial velocity on `ℝ^3` and every positive viscosity admit a
global smooth incompressible solution with uniformly bounded kinetic energy.
This is deliberately stronger than the manuscript-compatible restricted
whole-space surfaces considered later, so Lean keeps it as a regression target
for theorem-shape errors rather than as the final intended statement. -/
def ExplicitConcreteNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity,
    ExplicitConcreteNavierStokesRegularityClause ν u₀

/-- Repaired concrete problem data: smooth divergence-free initial velocity on
`ℝ^3` with positive viscosity and finite initial kinetic energy. -/
structure FiniteEnergyAdmissibleNavierStokesProblemData where
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  initialVelocity : NSInitialVelocity
  smooth_initial : smoothInitialVelocityData initialVelocity
  divergence_free_initial : ∀ x, initialSpatialDivergence initialVelocity x = 0
  finite_initial_energy : finiteInitialKineticEnergy initialVelocity

/-- Forget the finite-energy witness and view repaired concrete problem data on
the existing fully concrete theorem surface. -/
def FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData
    (P : FiniteEnergyAdmissibleNavierStokesProblemData) :
    NavierStokesProblemData mkFullyConcreteNavierStokesSurface where
  viscosity := P.viscosity
  viscosity_pos := P.viscosity_pos
  initialVelocity := P.initialVelocity
  smooth_initial := P.smooth_initial
  divergence_free_initial := P.divergence_free_initial

/-- Repaired structured whole-space theorem target: every smooth divergence-free
finite-energy initial datum admits a global regularity witness. -/
def FiniteEnergyConcreteNavierStokesMillenniumTarget : Prop :=
  ∀ P : FiniteEnergyAdmissibleNavierStokesProblemData,
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      P.toNavierStokesProblemData

/-- Repaired fully explicit global-regularity clause for fixed viscosity and
initial data on `ℝ^3`: the input side now explicitly requires finite initial
kinetic energy. -/
def ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
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

/-- Repaired explicit theorem target: every smooth divergence-free finite-energy
initial velocity on `ℝ^3` and every positive viscosity admit a global smooth
incompressible solution with uniformly bounded kinetic energy.  This is the
current local whole-space surface intended to stay compatible with reasonable
restricted `ℝ^3` routes, rather than the over-broad surrogate above. -/
def ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity,
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀

/-- The unrepaired explicit regularity clause immediately implies the repaired
finite-energy version, since the extra input hypothesis only narrows the class
of admissible data. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro hν hsmooth hdiv _hfinite
  exact h hν hsmooth hdiv

/-- The repaired explicit regularity clause is vacuous outside the finite-energy
input domain: if `u₀` fails finite initial kinetic energy, the clause holds for
purely logical reasons. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv hE
  exact False.elim (hfinite hE)

/-- The repaired structured whole-space input domain is also empty on any
initial datum that fails finite initial kinetic energy. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
    {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = u₀ } := by
  intro hP
  rcases hP with ⟨⟨P, hinit⟩⟩
  exact hfinite (hinit ▸ P.finite_initial_energy)

/-- For fixed positive viscosity and smooth divergence-free initial data, the
repaired structured whole-space input domain is inhabited exactly when the
datum has finite initial kinetic energy. -/
theorem nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = u₀ } ↔
      finiteInitialKineticEnergy u₀ := by
  constructor
  · intro hP
    rcases hP with ⟨⟨P, hPν, hPu₀⟩⟩
    exact hPu₀ ▸ P.finite_initial_energy
  · intro hfinite
    refine ⟨⟨{ viscosity := ν
               viscosity_pos := hν
               initialVelocity := u₀
               smooth_initial := hsmooth
               divergence_free_initial := hdiv
               finite_initial_energy := hfinite }, ?_⟩⟩
    exact ⟨rfl, rfl⟩

/-- On a fixed finite-energy datum, the repaired and unrepaired explicit
regularity clauses are equivalent. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ ↔
      ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  constructor
  · intro h hν hsmooth hdiv
    exact h hν hsmooth hdiv hfinite
  · intro h
    exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy h

/-- On a fixed finite-energy datum, the repaired explicit regularity clause can
be read directly as the unrepaired explicit clause. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy
      hfinite).mp h

/-- Therefore the unrepaired explicit whole-space theorem target immediately
subsumes the repaired finite-energy explicit target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  intro ν u₀
  exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy (h ν u₀)

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

/-- The fully concrete structured clause is equivalent to the fully explicit
PDE statement for the same viscosity and initial data. -/
theorem concreteNavierStokesGlobalRegularityClause_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }
      ↔
        ∃ u : NSVelocityField, ∃ p : NSPressureField,
          smoothSpaceTimeVelocity u ∧
          smoothSpaceTimePressure p ∧
          (∀ t x,
            timeVelocityDerivative u t x + spatialConvection u t x +
                spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          (∀ t x, spatialDivergence u t x = 0) ∧
          MatchesInitialVelocity u₀ u ∧
          boundedKineticEnergy u := by
  constructor
  · intro h
    rcases h with ⟨W⟩
    refine ⟨W.velocity, W.pressure, ?_⟩
    exact ⟨W.smooth_velocity, W.smooth_pressure, W.momentum_equation,
      W.incompressible, W.initial_condition, W.bounded_energy⟩
  · intro h
    rcases h with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
    refine ⟨({
      velocity := u
      pressure := p
      smooth_velocity := hu
      smooth_pressure := hp
      momentum_equation := hmom
      incompressible := hinc
      initial_condition := hinit
      bounded_energy := hbd
    } : NavierStokesGlobalRegularityWitness
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv })⟩

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause is equivalent to the repaired explicit regularity clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  constructor
  · intro h _hν _hsmooth _hdiv _hfinite
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  · intro h
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr
        (h hν hsmooth hdiv hfinite)

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause can be read directly as the unrepaired structured clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
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
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  have hRepaired :
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ :=
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mp h
  have hExplicit :
      ExplicitConcreteNavierStokesRegularityClause ν u₀ :=
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
      hRepaired hfinite
  exact
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr
      (hExplicit hν hsmooth hdiv)

/-- Conversely, on a fixed finite-energy datum, the unrepaired structured fully
concrete clause directly implies the repaired one. -/
theorem concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hExplicit : ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
    intro _hν _hsmooth _hdiv
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp h
  have hRepaired :
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ :=
    ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy hExplicit
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mpr hRepaired

/-- On a fixed finite-energy datum, the repaired structured fully concrete
clause is equivalent to the unrepaired one. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv } := by
  constructor
  · intro h
    exact
      finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
        hν hsmooth hdiv hfinite h
  · intro h
    exact
      concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
        hν hsmooth hdiv hfinite h

/-- The structured fully concrete target is equivalent to the literal explicit
NS theorem statement on `ℝ × ℝ^3`. -/
theorem ConcreteNavierStokesMillenniumTarget_iff_explicit :
    ConcreteNavierStokesMillenniumTarget ↔
      ExplicitConcreteNavierStokesMillenniumTarget := by
  constructor
  · intro h ν u₀ hν hsmooth hdiv
    simpa [ConcreteNavierStokesMillenniumTarget,
      ExplicitConcreteNavierStokesMillenniumTarget,
      ExplicitConcreteNavierStokesRegularityClause]
      using (concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp
          (h { viscosity := ν
               viscosity_pos := hν
               initialVelocity := u₀
               smooth_initial := hsmooth
               divergence_free_initial := hdiv })
  · intro h P
    have hExplicit := h P.viscosity P.initialVelocity P.viscosity_pos
      P.smooth_initial P.divergence_free_initial
    exact (concreteNavierStokesGlobalRegularityClause_iff
      (ν := P.viscosity) (u₀ := P.initialVelocity)
      P.viscosity_pos P.smooth_initial P.divergence_free_initial).mpr hExplicit

/-- The structured fully concrete theorem target directly implies the literal
explicit NS theorem statement on `ℝ × ℝ^3`. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitConcreteNavierStokesMillenniumTarget := by
  exact (ConcreteNavierStokesMillenniumTarget_iff_explicit).mp h

/-- The repaired structured whole-space theorem target is equivalent to the
corresponding fully explicit statement with finite-energy admissibility on the
input side. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit :
    FiniteEnergyConcreteNavierStokesMillenniumTarget ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  constructor
  · intro h ν u₀ hν hsmooth hdiv hfinite
    simpa [ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause]
      using
        (concreteNavierStokesGlobalRegularityClause_iff
          (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mp
            (h { viscosity := ν
                 viscosity_pos := hν
                 initialVelocity := u₀
                 smooth_initial := hsmooth
                 divergence_free_initial := hdiv
                 finite_initial_energy := hfinite })
  · intro h P
    have hExplicit :=
      h P.viscosity P.initialVelocity P.viscosity_pos
        P.smooth_initial P.divergence_free_initial P.finite_initial_energy
    exact
      (concreteNavierStokesGlobalRegularityClause_iff
        (ν := P.viscosity) (u₀ := P.initialVelocity)
        P.viscosity_pos P.smooth_initial P.divergence_free_initial).mpr hExplicit

/-- The repaired structured whole-space theorem target directly implies the
corresponding repaired explicit statement with finite-energy admissibility on
the input side. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact (FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit).mp h

/-- The unrepaired structured whole-space theorem target also directly implies
the repaired explicit theorem surface, by first forgetting to the unrepaired
explicit target and then using the finite-energy subsumption theorem there. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise, the unrepaired structured whole-space theorem target subsumes the
repaired structured finite-energy target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergy
    (h : ConcreteNavierStokesMillenniumTarget) :
    FiniteEnergyConcreteNavierStokesMillenniumTarget := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit).mpr
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Any restricted whole-space input class whose members all have finite
initial kinetic energy inherits the repaired explicit theorem surface.  This
packages later manuscript-compatible `ℝ^3` routes, such as Schwartz-style
initial data, without fixing a decay notion in this file. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_apply_of_inputClass
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {InputClass : NSInitialVelocity → Prop}
    (hfinite : ∀ ⦃u₀ : NSInitialVelocity⦄, InputClass u₀ → finiteInitialKineticEnergy u₀)
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hu₀ : InputClass u₀)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      boundedKineticEnergy u := by
  exact h ν u₀ hν hsmooth hdiv (hfinite hu₀)

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

/-- In the fully differential-side concrete kit, the momentum equation is
literally the NS equation with explicit `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteDifferentialOperators
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- In the same fully differential-side concrete kit, incompressibility is still
exactly the vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDifferentialOperators
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same fully differential-side concrete kit. -/
theorem divergenceFreeInitialData_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperators
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- On the stronger theorem surface, the velocity smoothness predicate is
literally `C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothVelocity_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u : NSVelocityField} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothVelocity u
      ↔ ContDiff ℝ ∞ (spaceTimeVelocityMap u) := by
  rfl

/-- Likewise, the pressure smoothness predicate is literally `C^∞` smoothness
on `ℝ × ℝ^3`. -/
theorem smoothPressure_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {p : NSPressureField} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothPressure p
      ↔ ContDiff ℝ ∞ (spaceTimePressureMap p) := by
  rfl

/-- Likewise, the initial-data smoothness predicate is literally `C^∞`
smoothness on `ℝ^3`. -/
theorem smoothInitialData_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothInitialData u₀
      ↔ ContDiff ℝ ∞ u₀ := by
  rfl

/-- On the stronger theorem surface, the momentum equation still literally uses
the explicit differential operators `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- Incompressibility remains the explicit vanishing of the spatial divergence
on the stronger theorem surface. -/
theorem isIncompressible_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition on the
stronger theorem surface. -/
theorem divergenceFreeInitialData_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- On the fully concrete theorem surface, the bounded-energy predicate is
literally uniform boundedness of the kinetic energy integrals. -/
theorem boundedEnergy_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    mkFullyConcreteNavierStokesSurface.boundedEnergy u
      ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
          MeasureTheory.Integrable (fun x => ‖u t x‖ ^ (2 : ℕ)) ∧
            (∫ x, ‖u t x‖ ^ (2 : ℕ) ∂(MeasureTheory.volume : MeasureTheory.Measure NSSpace)) ≤ C := by
  rfl

/-- The fully concrete theorem surface still literally uses the explicit NS
operators `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkFullyConcreteNavierStokesSurface_iff
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation mkFullyConcreteNavierStokesSurface ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- On the fully concrete theorem surface, incompressibility is literally the
vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    IsIncompressible mkFullyConcreteNavierStokesSurface u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- On the fully concrete theorem surface, velocity smoothness is literal
`C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothVelocity_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    mkFullyConcreteNavierStokesSurface.smoothVelocity u
      ↔ ContDiff ℝ ∞ (spaceTimeVelocityMap u) := by
  rfl

/-- On the fully concrete theorem surface, pressure smoothness is literal
`C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothPressure_mkFullyConcreteNavierStokesSurface_iff
    {p : NSPressureField} :
    mkFullyConcreteNavierStokesSurface.smoothPressure p
      ↔ ContDiff ℝ ∞ (spaceTimePressureMap p) := by
  rfl

/-- On the fully concrete theorem surface, initial-data smoothness is literal
`C^∞` smoothness on `ℝ^3`. -/
theorem smoothInitialData_mkFullyConcreteNavierStokesSurface_iff
    {u₀ : NSInitialVelocity} :
    mkFullyConcreteNavierStokesSurface.smoothInitialData u₀
      ↔ ContDiff ℝ ∞ u₀ := by
  rfl

/-- On the fully concrete theorem surface, divergence-free initial data are
literally the vanishing of the explicit initial divergence. -/
theorem divergenceFreeInitialData_mkFullyConcreteNavierStokesSurface_iff
    {u₀ : NSInitialVelocity} :
    mkFullyConcreteNavierStokesSurface.divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
