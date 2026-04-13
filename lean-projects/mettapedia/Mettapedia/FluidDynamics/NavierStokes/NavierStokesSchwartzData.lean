import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationTarget
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Navier-Stokes Schwartz Initial Data

This file packages a manuscript-compatible restricted whole-space input lane for
Schwartz-class initial data on `ℝ^3`.  The current local whole-space theorem
surface is phrased on smooth finite-energy data; here we prove that Schwartz
data automatically satisfy those input hypotheses and therefore inherit the
repaired theorem target directly.

This is the local insertion point for the manuscript's torus-to-`ℝ^3`
Schwartz-data route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff SchwartzMap

/-- Schwartz-class initial velocities on `ℝ^3`. -/
abbrev NSSchwartzInitialVelocity : Type := SchwartzMap NSSpace NSSpace

/-- Schwartz initial data are smooth in the concrete `ℝ^3` sense used by the
local Navier-Stokes theorem surface. -/
theorem smoothInitialVelocityData_of_schwartzInitialVelocity
    (u₀ : NSSchwartzInitialVelocity) :
    smoothInitialVelocityData (u₀ : NSSpace → NSSpace) := by
  unfold smoothInitialVelocityData
  simpa using u₀.smooth (⊤ : ℕ∞)

/-- Schwartz initial data have finite kinetic energy on `ℝ^3`. -/
theorem finiteInitialKineticEnergy_of_schwartzInitialVelocity
    (u₀ : NSSchwartzInitialVelocity) :
    finiteInitialKineticEnergy (u₀ : NSSpace → NSSpace) := by
  simpa [finiteInitialKineticEnergy, initialKineticEnergyDensity] using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
      u₀.continuous.aestronglyMeasurable).mp
      (u₀.memLp 2 (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)))

/-- Explicit repaired whole-space regularity clause specialized to
Schwartz-class initial data.  Smoothness and finite initial energy are omitted
from the hypotheses because they are automatic on this input class. -/
def ExplicitSchwartzAdmissibleNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSSchwartzInitialVelocity) : Prop :=
  0 < ν →
    (∀ x, initialSpatialDivergence (u₀ : NSSpace → NSSpace) x = 0) →
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
        smoothSpaceTimeVelocity u ∧
        smoothSpaceTimePressure p ∧
        (∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x) ∧
        (∀ t x, spatialDivergence u t x = 0) ∧
        MatchesInitialVelocity (u₀ : NSSpace → NSSpace) u ∧
        boundedKineticEnergy u

/-- The specialized Schwartz-data clause is exactly the repaired whole-space
clause restricted to a Schwartz input. -/
theorem ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff
    {ν : ℝ} {u₀ : NSSchwartzInitialVelocity} :
    ExplicitSchwartzAdmissibleNavierStokesRegularityClause ν u₀ ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (u₀ : NSSpace → NSSpace) := by
  constructor
  · intro h hν _hsmooth hdiv _hfinite
    exact h hν hdiv
  · intro h hν hdiv
    exact
      h hν
        (smoothInitialVelocityData_of_schwartzInitialVelocity u₀)
        hdiv
        (finiteInitialKineticEnergy_of_schwartzInitialVelocity u₀)

/-- Explicit whole-space theorem target restricted to Schwartz-class initial
data on `ℝ^3`. -/
def ExplicitSchwartzAdmissibleNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSSchwartzInitialVelocity,
    ExplicitSchwartzAdmissibleNavierStokesRegularityClause ν u₀

/-- The repaired finite-energy whole-space theorem surface immediately yields
the corresponding Schwartz-data target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_schwartzTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitSchwartzAdmissibleNavierStokesMillenniumTarget := by
  intro ν u₀
  exact
    (ExplicitSchwartzAdmissibleNavierStokesRegularityClause_iff
      (ν := ν) (u₀ := u₀)).2
      (h ν (u₀ : NSSpace → NSSpace))

/-- Apply the repaired whole-space theorem target directly to a Schwartz input. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_apply_of_schwartzInitialVelocity
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSSchwartzInitialVelocity} :
    ExplicitSchwartzAdmissibleNavierStokesRegularityClause ν u₀ := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_schwartzTarget
      h ν u₀

end NavierStokes
end FluidDynamics
end Mettapedia
