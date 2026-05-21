import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Finite-Mode Uniform Continuation Clause Packaging

This file records the older uniform-vorticity continuation surface for the
bounded two-mode Schwartz ansatz.  Once the pointwise Navier--Stokes momentum
equation is closed for that ansatz, the finite-mode bounded-energy route has
already produced explicit global output on `ℝ^3`; here we repackage that exact
output as uniform-vorticity continuation clauses on every time horizon.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A bounded two-mode Schwartz ansatz satisfying the full pointwise
Navier--Stokes equation already inhabits the explicit uniform-vorticity
continuation clause on every horizon, because the finite-mode bounded-energy
route has already produced whole-space explicit global output on the same
datum. -/
theorem ExplicitUniformVorticityContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitUniformVorticityContinuationClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
        (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
          ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq))) T

/-- The same bounded two-mode Schwartz exact closure also inhabits the repaired
finite-energy uniform-vorticity continuation clause on every horizon. -/
theorem
    ExplicitFiniteEnergyUniformVorticityContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)) T

end NavierStokes
end FluidDynamics
end Mettapedia
