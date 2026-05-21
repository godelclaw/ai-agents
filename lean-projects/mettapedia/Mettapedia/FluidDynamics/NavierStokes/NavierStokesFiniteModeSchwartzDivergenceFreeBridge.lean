import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDivergenceFreeData

/-!
# Finite-Mode Bridge to Schwartz Divergence-Free Data

This file connects the bounded two-mode Schwartz ansatz to the manuscript-style
`Sσ(ℝ^3)` input lane.  Once the two-mode construction satisfies the pointwise
momentum equation and the profile-level divergence conditions, the repaired
whole-space clauses on `ℝ^3` restrict immediately to the corresponding
Schwartz divergence-free clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Package a two-mode Schwartz initial slice as manuscript-style divergence-free
Schwartz data when the spatial profiles are divergence-free. -/
def twoModeSchwartzDivergenceFreeInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    NSSchwartzDivergenceFreeInitialVelocity :=
  ⟨(a0 • f + b0 • g : NSSchwartzInitialVelocity),
    initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
      a0 b0 f g hfDiv hgDiv⟩

/-- The bounded two-mode Schwartz ansatz reaches the manuscript-style explicit
`Sσ(ℝ^3)` clause once its pointwise momentum equation is supplied. -/
theorem
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_twoModeSchwartzDivergenceFreeInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
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
    ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause
      ν
      (twoModeSchwartzDivergenceFreeInitialVelocity
        (a 0) (b 0) f g hfDiv hgDiv) := by
  exact
    (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_iff
      (ν := ν)
      (u₀ := twoModeSchwartzDivergenceFreeInitialVelocity
        (a 0) (b 0) f g hfDiv hgDiv)).2 <|
      by
        simpa [twoModeSchwartzDivergenceFreeInitialVelocity, twoModeSchwartzInitialVelocity] using
          (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
            ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

/-- The same bounded two-mode Schwartz ansatz therefore reaches the
manuscript-style structured `Sσ(ℝ^3)` clause as well. -/
theorem
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_twoModeSchwartzDivergenceFreeInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
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
    StructuredSchwartzDivergenceFreeNavierStokesRegularityClause
      ν
      (twoModeSchwartzDivergenceFreeInitialVelocity
        (a 0) (b 0) f g hfDiv hgDiv) := by
  exact
    (StructuredSchwartzDivergenceFreeNavierStokesRegularityClause_iff
      (ν := ν)
      (u₀ := twoModeSchwartzDivergenceFreeInitialVelocity
        (a 0) (b 0) f g hfDiv hgDiv)).2
      (ExplicitSchwartzDivergenceFreeNavierStokesRegularityClause_twoModeSchwartzDivergenceFreeInitialVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

end NavierStokes
end FluidDynamics
end Mettapedia
