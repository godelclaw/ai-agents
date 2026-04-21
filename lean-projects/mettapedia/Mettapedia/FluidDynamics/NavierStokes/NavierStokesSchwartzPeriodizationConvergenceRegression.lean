import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationConvergence

/-!
# Navier-Stokes Schwartz Periodization Convergence Regression

Small theorem-level checks for the local cube convergence interface above the
finite box periodization family.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzPeriodizationConvergenceRegression

open Filter

/-- Zero data inhabit the manuscript-style `Sσ(ℝ^3)` input class. -/
def zeroSchwartzDivergenceFreeInitialVelocity :
    NSSchwartzDivergenceFreeInitialVelocity :=
  ⟨0, by
    intro x
    simpa using (initialSpatialDivergence_zero x)⟩

theorem boxedPartialPeriodizationConvergesOnCube_zero_regression
    (R L : ℝ) :
    BoxedPartialPeriodizationConvergesOnCube R L
      (0 : NSInitialVelocity) (0 : NSInitialVelocity) := by
  intro x hx
  simp [boxedPartialPeriodizedInitialVelocity, finitePartialPeriodizedInitialVelocity]

theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_zero_regression
    (R L : ℝ) :
    ∀ x ∈ spatialCube R,
      Filter.Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (0 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
    (boxedPartialPeriodizationConvergesOnCube_zero_regression R L)

theorem boxedPartialPeriodizationConvergesOnCube_zero_schwartzDivergenceFree_regression
    (R L : ℝ) :
    BoxedPartialPeriodizationConvergesOnCube R L
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity)
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) := by
  simpa using boxedPartialPeriodizationConvergesOnCube_zero_regression R L

theorem boxedPartialPeriodizationConvergesOnCube_zero_schwartzDivergenceFree_interface_regression
    {R L : ℝ} (hL : L ≠ 0) :
    BoxedPartialPeriodizationConvergesOnCube R L
      (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L zeroSchwartzDivergenceFreeInitialVelocity.1) := by
  exact
    BoxedPartialPeriodizationConvergesOnCube_of_schwartzDivergenceFree
      (R := R) hL zeroSchwartzDivergenceFreeInitialVelocity

theorem boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_tendsto_regression
    {L : ℝ} (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) (x : NSSpace) :
    Filter.Tendsto
      (fun N => (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1 x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  exact boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_tendsto hL u₀ x

theorem schwartzPeriodizedInitialVelocity_periodic_regression
    (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (k : NSLatticeIndex) (x : NSSpace) :
    schwartzPeriodizedInitialVelocity L u₀.1 (x + periodizationShift L k) =
      schwartzPeriodizedInitialVelocity L u₀.1 x := by
  exact schwartzPeriodizedInitialVelocity_add_periodizationShift L u₀.1 k x

theorem boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData_initialVelocity_tendsto_regression
    {ν L : ℝ} (hν : 0 < ν) (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) (x : NSSpace) :
    Filter.Tendsto
      (fun N =>
        (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).initialVelocity x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  exact
    boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData_initialVelocity_tendsto
      hν hL u₀ x

theorem boxedPartialPeriodizationNavierStokesProblemData_initialVelocity_tendsto_regression
    {ν L : ℝ} (hν : 0 < ν) (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) (x : NSSpace) :
    Filter.Tendsto
      (fun N => (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  exact boxedPartialPeriodizationNavierStokesProblemData_initialVelocity_tendsto hν hL u₀ x

theorem finiteEnergyTarget_apply_boxedPartialPeriodization_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    NavierStokesGlobalRegularityClause mkFullyConcreteNavierStokesSurface
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_apply_boxedPartialPeriodization
      h hν N L u₀

theorem boxedPartialPeriodizationSteadySeed_basic_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      (∀ t x,
        timeVelocityDerivative (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      (∀ t,
        kineticEnergyDensity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t =
          initialKineticEnergyDensity
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity) := by
  exact boxedPartialPeriodizationSteadySeed_basic hν N L u₀

theorem boxedPartialPeriodizationSteadySeed_momentum_zero_time_obstruction_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} (hT : 0 ≤ T) (p : NSPressureField)
    (hmom :
      ∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ∀ x,
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x := by
  exact
    boxedPartialPeriodizationSteadySeed_momentum_zero_time_obstruction
      hν N L u₀ hT p hmom

theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_zero_schwartz_regression
    {R L : ℝ} (hL : L ≠ 0) :
    ∀ x ∈ spatialCube R,
      Filter.Tendsto
        (fun N =>
          boxedPeriodizationShellInitialVelocity N L
            (zeroSchwartzDivergenceFreeInitialVelocity.1 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  simpa using
    boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_schwartzDivergenceFree
      (R := R) hL zeroSchwartzDivergenceFreeInitialVelocity

end NavierStokesSchwartzPeriodizationConvergenceRegression
end NavierStokes
end FluidDynamics
end Mettapedia
