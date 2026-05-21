import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionVelocityRouteObstruction

/-!
# Finite-Mode Velocity-Route Construction

This file packages positive inhabitants of the bundled pressure-agnostic
witness-construction velocity route from the bounded two-mode Schwartz ansatz.

Once the full pointwise Navier--Stokes momentum equation is supplied on the
divergence-free Schwartz lane, the existing finite-mode infrastructure already
produces an exact finite-time witness for the same velocity and pressure.  The
same boundedness hypotheses also provide a BKM envelope for that velocity, so
the bundled route is inhabited constructively rather than only analyzed
negatively.

As a concrete bottom-up instance, the file specializes this to the nonzero
constant-one two-mode branch at positive viscosity, under the exact
compensating pressure-gradient hypothesis that cancels the viscous Laplacian
residual.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A bounded two-mode divergence-free Schwartz ansatz satisfying the full
pointwise momentum equation yields one explicit finite-time witness whose
velocity also carries a BKM envelope.  Hence the same velocity inhabits the
bundled pressure-agnostic witness-construction route. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_exact_BKMContinuationPremise_and_velocityRoute_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
      W.velocity = twoModeSchwartzVelocity a b f g ∧
        W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
        (∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint) ∧
        VelocityWitnessConstructionRoute
          ν
          T
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity)
          (twoModeSchwartzVelocity a b f g) := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a b f g A B T haBound hbBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWvel, hWpress, ?_, ?_⟩
  · refine ⟨Ω, Bint, ?_, hInt⟩
    simpa [hWvel] using hEnv
  · exact Or.inl ⟨W, hWvel⟩

/-- Route-only corollary of the previous exact finite-time witness and BKM
envelope construction. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_velocityRoute_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    VelocityWitnessConstructionRoute
      ν
      T
      ((twoModeSchwartzDivergenceFreeInitialVelocity
        (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity)
      (twoModeSchwartzVelocity a b f g) := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_exact_BKMContinuationPremise_and_velocityRoute_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨_W, _hWvel, _hWpress, _hBKM, hRoute⟩
  exact hRoute

/-- Concrete positive-viscosity specialization: once the constant-one two-mode
branch is supplied with the exact compensating affine-plus-Schwartz pressure
gradient, the same nonzero velocity again carries an exact finite-time
witness, a BKM continuation premise, and an inhabitant of the bundled
pressure-agnostic witness-construction route. -/
theorem
    oneOneTwoModeSchwartzVelocity_nonzero_and_posViscosity_pressureRepair_exhibits_exact_BKMContinuationPremise_and_velocityRoute_of_inviscidClosure_pressureGradient
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hpressure : ∀ t x,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          (∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
          VelocityWitnessConstructionRoute
            ν
            T
            (twoModeSchwartzInitialVelocity 1 1 f g)
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) := by
  rcases
      oneOneTwoModeSchwartzVelocity_nonzero_posViscosity_BKMPremise_of_inviscidClosure_pressureGradient
        (ν := ν) (T := T) hν f g c π ρ q hc hπ hρ hfg hfDiv hgDiv hclosure hpressure with
    ⟨hnonzero, W, hWvel, hWpress, Ω, Bint, hEnv, hInt⟩
  refine ⟨hnonzero, W, hWvel, hWpress, ?_, ?_⟩
  · exact ⟨Ω, Bint, hEnv, hInt⟩
  · exact Or.inl ⟨W, hWvel⟩

end NavierStokes
end FluidDynamics
end Mettapedia
