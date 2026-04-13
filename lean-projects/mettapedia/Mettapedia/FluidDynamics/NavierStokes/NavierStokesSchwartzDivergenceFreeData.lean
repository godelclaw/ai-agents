import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzData

/-!
# Navier-Stokes Schwartz Divergence-Free Initial Data

This file refines the local whole-space Schwartz lane to the manuscript's
`Sσ(ℝ^3)` input class: Schwartz vector fields on `ℝ^3` whose initial
divergence vanishes.  Smoothness and finite initial kinetic energy are still
automatic from the Schwartz hypothesis, while the divergence-free condition is
carried directly in the input type.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff SchwartzMap

/-- Schwartz-class divergence-free initial velocities on `ℝ^3`. -/
abbrev NSSchwartzDivergenceFreeInitialVelocity : Type :=
  { u₀ : NSSchwartzInitialVelocity //
      ∀ x, initialSpatialDivergence (u₀ : NSSpace → NSSpace) x = 0 }

/-- Manuscript-style `Sσ(ℝ^3)` data are smooth in the local concrete
`ℝ^3` sense. -/
theorem smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    smoothInitialVelocityData (u₀.1 : NSSpace → NSSpace) := by
  exact smoothInitialVelocityData_of_schwartzInitialVelocity u₀.1

/-- Manuscript-style `Sσ(ℝ^3)` data have finite initial kinetic energy. -/
theorem finiteInitialKineticEnergy_of_schwartzDivergenceFreeInitialVelocity
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    finiteInitialKineticEnergy (u₀.1 : NSSpace → NSSpace) := by
  exact finiteInitialKineticEnergy_of_schwartzInitialVelocity u₀.1

/-- Divergence freeness is built into the manuscript-style `Sσ(ℝ^3)` input
type. -/
theorem divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    ∀ x, initialSpatialDivergence (u₀.1 : NSSpace → NSSpace) x = 0 := by
  exact u₀.2

/-- Explicit repaired whole-space regularity clause specialized to the
manuscript's `Sσ(ℝ^3)` input class.  Smoothness, finite initial energy, and
divergence freeness are omitted from the hypotheses because they are automatic
on this subtype. -/
def ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) : Prop :=
  0 < ν →
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (u₀.1 : NSSpace → NSSpace) u ∧
      boundedKineticEnergy u

/-- The `Sσ(ℝ^3)` clause is exactly the earlier Schwartz clause with the
divergence-free hypothesis discharged by the subtype. -/
theorem ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff_schwartzClause
    {ν : ℝ} {u₀ : NSSchwartzDivergenceFreeInitialVelocity} :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀ ↔
      ExplicitSchwartzAdmissibleNavierStokesRegularityClause ν u₀.1 := by
  constructor
  · intro h hν _hdiv
    exact h hν
  · intro h hν
    exact h hν u₀.2

/-- The `Sσ(ℝ^3)` clause is exactly the repaired whole-space clause restricted
to the manuscript's divergence-free Schwartz input class. -/
theorem ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff
    {ν : ℝ} {u₀ : NSSchwartzDivergenceFreeInitialVelocity} :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀ ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (u₀.1 : NSSpace → NSSpace) := by
  constructor
  · intro h
    exact
      (ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀.1)).1 <|
      (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff_schwartzClause
        (ν := ν) (u₀ := u₀)).1 h
  · intro h
    exact
      (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff_schwartzClause
        (ν := ν) (u₀ := u₀)).2 <|
      (ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀.1)).2 h

/-- Explicit whole-space theorem target restricted to manuscript-style
divergence-free Schwartz initial data on `ℝ^3`. -/
def ExplicitSchwartzDivergenceFreeNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSSchwartzDivergenceFreeInitialVelocity,
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀

/-- The earlier Schwartz-data theorem surface immediately yields the
manuscript-style `Sσ(ℝ^3)` target. -/
theorem ExplicitSchwartzAdmissibleNavierStokesMillenniumTarget_implies_schwartzDivergenceFreeTarget
    (h : ExplicitSchwartzAdmissibleNavierStokesMillenniumTarget) :
    ExplicitSchwartzDivergenceFreeNavierStokesMillenniumTarget := by
  intro ν u₀
  exact
    (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff_schwartzClause
      (ν := ν) (u₀ := u₀)).2
      (h ν u₀.1)

/-- The repaired finite-energy whole-space theorem surface immediately yields
the manuscript-style `Sσ(ℝ^3)` target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_schwartzDivergenceFreeTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitSchwartzDivergenceFreeNavierStokesMillenniumTarget := by
  exact
    ExplicitSchwartzAdmissibleNavierStokesMillenniumTarget_implies_schwartzDivergenceFreeTarget
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_schwartzTarget h)

/-- Apply the repaired whole-space theorem target directly to a manuscript-style
`Sσ(ℝ^3)` input. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_apply_of_schwartzDivergenceFreeInitialVelocity
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSSchwartzDivergenceFreeInitialVelocity} :
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀ := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_schwartzDivergenceFreeTarget
      h ν u₀

/-- A manuscript-style `Sσ(ℝ^3)` datum with positive viscosity canonically
produces repaired finite-energy whole-space problem data. -/
def NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {ν : ℝ} (hν : 0 < ν) :
    FiniteEnergyAdmissibleNavierStokesProblemData where
  viscosity := ν
  viscosity_pos := hν
  initialVelocity := (u₀.1 : NSSpace → NSSpace)
  smooth_initial :=
    smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀
  divergence_free_initial :=
    divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀
  finite_initial_energy :=
    finiteInitialKineticEnergy_of_schwartzDivergenceFreeInitialVelocity u₀

/-- Structured repaired whole-space regularity clause specialized to the
manuscript's `Sσ(ℝ^3)` input class. -/
def StructuredSchwartzDivergenceFreeNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) : Prop :=
  ∀ hν : 0 < ν,
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      (u₀.toFiniteEnergyAdmissibleNavierStokesProblemData hν).toNavierStokesProblemData

/-- On manuscript-style `Sσ(ℝ^3)` data, the structured repaired clause is
equivalent to the specialized explicit clause. -/
theorem StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_iff
    {ν : ℝ} {u₀ : NSSchwartzDivergenceFreeInitialVelocity} :
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀ ↔
      ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀ := by
  constructor
  · intro h hν
    have hStructured :=
      h hν
    have hFiniteEnergy :
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
          ν (u₀.1 : NSSpace → NSSpace) := by
      simpa [NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData]
        using
          (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
            (ν := ν) (u₀ := (u₀.1 : NSSpace → NSSpace))
            hν
            (smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
            (divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
            (finiteInitialKineticEnergy_of_schwartzDivergenceFreeInitialVelocity u₀)).mp
            hStructured
    exact
      (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀)).2 hFiniteEnergy hν
  · intro h hν
    have hFiniteEnergy :
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
          ν (u₀.1 : NSSpace → NSSpace) :=
      (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀)).1 h
    simpa [NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData]
      using
        (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
          (ν := ν) (u₀ := (u₀.1 : NSSpace → NSSpace))
          hν
          (smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
          (divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
          (finiteInitialKineticEnergy_of_schwartzDivergenceFreeInitialVelocity u₀)).2
          hFiniteEnergy

/-- Structured repaired whole-space theorem target restricted to the
manuscript's `Sσ(ℝ^3)` input class. -/
def StructuredSchwartzDivergenceFreeNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSSchwartzDivergenceFreeInitialVelocity,
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause ν u₀

/-- The structured and explicit `Sσ(ℝ^3)` theorem surfaces are equivalent. -/
theorem StructuredSchwartzDivergenceFreeNavierStokesMillenniumTarget_iff
    :
    StructuredSchwartzDivergenceFreeNavierStokesMillenniumTarget ↔
      ExplicitSchwartzDivergenceFreeNavierStokesMillenniumTarget := by
  constructor
  · intro h ν u₀
    exact
      (StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀)).1
        (h ν u₀)
  · intro h ν u₀
    exact
      (StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_iff
        (ν := ν) (u₀ := u₀)).2
        (h ν u₀)

/-- The repaired structured whole-space theorem target immediately yields the
manuscript-style structured `Sσ(ℝ^3)` target. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_structuredSchwartzDivergenceFreeTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    StructuredSchwartzDivergenceFreeNavierStokesMillenniumTarget := by
  intro ν u₀ hν
  exact h (u₀.toFiniteEnergyAdmissibleNavierStokesProblemData hν)

end NavierStokes
end FluidDynamics
end Mettapedia
