import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergy

/-!
# Finite-Mode BKM Clause Packaging

This file records the next exact consequence of the bounded two-mode Schwartz
ansatz.  Once the pointwise Navier--Stokes momentum equation is closed for that
ansatz, the existing finite-mode bounded-energy module already gives explicit
global output on `ℝ^3`.  Here we repackage that exact global output as concrete
BKM continuation clauses on every time horizon.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A bounded two-mode Schwartz ansatz satisfying the full pointwise
Navier--Stokes equation already inhabits the explicit BKM continuation clause
on every slab `0 ≤ t ≤ T`, because the finite-mode bounded-energy route has
already produced a whole-space global output for the same datum. -/
theorem ExplicitBKMContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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
    ExplicitBKMContinuationClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
        (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
          ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq))) T

/-- The same bounded two-mode Schwartz exact closure also inhabits the repaired
finite-energy BKM continuation clause on every horizon.  This is the precise
finite-energy continuation surface matched to the current grassroots route. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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
    ExplicitFiniteEnergyBKMContinuationClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)) T

/-- At the BKM-clause level, an equal-amplitude anti-profile initial datum is
exactly the zero initial datum.  This records that the unrepaired continuation
clause contains no residual information about the cancelled two-mode profile. -/
theorem ExplicitBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T ↔
      ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  simp [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero a0 f]

/-- The same exact normalization on the repaired finite-energy BKM clause
surface.  Any finite-energy BKM clause for the equal-amplitude anti-profile
initial slice is just the zero-datum clause. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_iff_zero
    (ν T a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity a0 a0 f (-f)) T ↔
      ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  simp [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero a0 f]

end NavierStokes
end FluidDynamics
end Mettapedia
