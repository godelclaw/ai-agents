import Mathlib.Analysis.Calculus.MeanValue
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzDivergenceFreeBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Finite-Mode Bridge to the BKM Premise

This file pushes the bounded two-mode Schwartz ansatz one layer deeper into the
continuation machinery.  Beyond the repaired whole-space theorem surfaces, the
same divergence-free Schwartz datum also yields an explicit finite-time witness;
when a slabwise uniform vorticity bound is supplied, that witness carries an
integrable BKM envelope as well.  For bounded scalar amplitudes, the imported
finite-mode vorticity estimates provide that envelope directly.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The bounded two-mode divergence-free Schwartz ansatz produces an exact
finite-time witness once its pointwise momentum equation is supplied. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
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
          W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
  simpa [twoModeSchwartzDivergenceFreeInitialVelocity, twoModeSchwartzInitialVelocity] using
    (show ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q from
      ⟨ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
          (ν := ν) (T := T)
          a b f g A B c π ρ q
          ha hb hc hπ hρ hfDiv hgDiv hν haBound hbBound heq,
        rfl, rfl⟩)

/-- With a slabwise uniform vorticity bound in hand, the same exact two-mode
divergence-free Schwartz witness already inhabits the repaired BKM continuation
premise. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_and_uniformVorticityBound
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T K : ℝ}
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
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hω : uniformVorticityBoundUpTo (twoModeSchwartzVelocity a b f g) T K) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      uniformVorticityBoundUpTo_implies_BKMEnvelope
        (u := twoModeSchwartzVelocity a b f g) (T := T) (B := K) hω with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The bounded two-mode divergence-free Schwartz ansatz already carries its
own BKM envelope once the scalar amplitudes are uniformly bounded, so the BKM
premise does not need an extra vorticity hypothesis on top of the momentum and
boundedness inputs. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation
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
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a b f g A B T haBound hbBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The constant-one two-profile inviscid zero-pressure branch leaves the
cancelled anti-profile cell: if the two Schwartz profiles do not cancel
pointwise everywhere and their explicit convection closure vanishes, then the
branch is genuinely nonzero and its finite-time witness already carries a BKM
envelope. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  refine
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg, ?_⟩
  let W :=
    ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
      f g hfDiv hgDiv hclosure (T := T)
  have hWvel :
      W.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
    rfl
  have hWpressure : W.pressure = (0 : NSPressureField) := by
    have hWpressureAffine :
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) := by
      rfl
    have hAffineZero :
        affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
          (0 : NSPressureField) := by
      funext t x
      simp [affineAddScalarSchwartzPressure]
    exact hWpressureAffine.trans hAffineZero
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp) (by intro t; simp) with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWvel, hWpressure, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- Positive-viscosity version of the non-cancelling constant-one branch with
the exact compensating pressure-gradient hypothesis.  The previous zero
pressure theorem is blocked by the viscous Laplacian residual; this theorem
records the minimal pressure repair that makes the same nonzero finite-mode
velocity and its internally supplied BKM envelope available again. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_posViscosity_BKMPremise_of_inviscidClosure_pressureGradient
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
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  refine
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg, ?_⟩
  have hmom :
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
    exact
      (momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
        ν (affineAddScalarSchwartzPressure c π ρ q) f g hclosure).2 hpressure
  let W :=
    ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (a := fun _ : NSTime => 1)
      (b := fun _ : NSTime => 1)
      (f := f)
      (g := g)
      (A := 1)
      (B := 1)
      (c := c)
      (π := π)
      (ρ := ρ)
      (q := q)
      (ν := ν)
      (T := T)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      hc
      hπ
      hρ
      hfDiv
      hgDiv
      hν.le
      (by intro t; simp)
      (by intro t; simp)
      hmom
  have hWvel :
      W.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
    rfl
  have hWpressure : W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
    rfl
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp) (by intro t; simp) with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWvel, hWpressure, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The bounded two-mode divergence-free Schwartz ansatz also produces an
exact finite-time witness for arbitrary time-indexed Schwartz pressure slices,
once the pressure field is smooth and the pointwise momentum equation is
supplied.  This is the pressure-slice analogue of the affine-plus-localized
pressure witness above. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = (fun s : NSTime => fun y : NSSpace => q s y) := by
  simpa [twoModeSchwartzDivergenceFreeInitialVelocity, twoModeSchwartzInitialVelocity] using
    (show ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = (fun s : NSTime => fun y : NSSpace => q s y) from
      ⟨ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
          (ν := ν) (T := T)
          (u₀ := twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
          a (deriv a) b (deriv b) f g A B q
          (by simpa [twoModeSchwartzVelocity] using
            smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g)
          hp
          (by simpa [twoModeSchwartzVelocity] using
            MatchesInitialVelocity_twoModeSchwartzVelocity a b f g)
          hν haBound hbBound
          (hasDerivAt_deriv_of_contDiff ha)
          (hasDerivAt_deriv_of_contDiff hb)
          (by
            intro t x
            simpa [twoModeSchwartzVelocity] using heq t x)
          (by
            intro t x
            simpa [twoModeSchwartzVelocity] using
              spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv t x),
        rfl, rfl⟩)

/-- For the same pressure-slice class, bounded scalar amplitudes provide the
BKM-envelope part internally through the finite-mode vorticity estimate.  Thus
the BKM premise is reduced to smooth pressure, bounded amplitudes,
profile-level divergence freedom, and the pointwise momentum equation. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
        ha hb f g A B q hp hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a b f g A B T haBound hbBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The pressure-slice BKM premise can be driven by an explicit finite-mode
residual closure instead of an opaque pointwise momentum-equation hypothesis.
This exposes the exact remaining closure obligation for the two-mode Schwartz
ansatz: scalar amplitude derivatives, the four self/mixed convection terms, the
pressure-slice gradient, and the two linear Laplacian terms. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
      deriv a t • f x + deriv b t • g x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              (b t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x) +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
      ha hb f g A B q hp hν haBound hbBound hfDiv hgDiv
      (momentumEquation_twoModeSchwartzVelocity_schwartzPressureSlice_of_explicitClosure
        ha hb ν f g q hclosure)

/-- The anti-profile cancellation baseline reaches the pressure-slice BKM
premise through the expanded residual-closure route.  The resulting initial
datum is zero, but the theorem records that the explicit closure bridge accepts
the cancellation pair `f, -f` whenever `f` is divergence-free. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_oneOneAntiProfile_schwartzPressureSlice_zeroPressure
    {ν T : ℝ} (hν : 0 ≤ ν) (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hPremise :=
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := fun _ : NSTime => 1)
      (b := fun _ : NSTime => 1)
      (f := f)
      (g := -f)
      (A := 1)
      (B := 1)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := ν)
      (T := T)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      hp
      hν
      (by intro t; simp)
      (by intro t; simp)
      hfDiv
      hgDiv
      (by
        intro t x
        simpa using
          explicitClosure_oneOneAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
            ν f t x)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity 1 1 f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hPremise
  simpa using hPremise

/-- The anti-profile pressure-slice BKM baseline remains valid for any smooth
equal amplitude with a uniform scalar bound.  The datum and velocity still
cancel to zero; the theorem records that the expanded residual-closure route
does not depend on the artificial constant-one amplitude choice. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hPremise :=
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := a)
      (b := a)
      (f := f)
      (g := -f)
      (A := A)
      (B := A)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := ν)
      (T := T)
      ha
      ha
      hp
      hν
      haBound
      haBound
      hfDiv
      hgDiv
      (by
        intro t x
        simpa using
          explicitClosure_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
            ha ν f t x)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hPremise
  simpa using hPremise

/-- Sharpened audit form of the equal-amplitude anti-profile pressure-slice
BKM baseline: the witness produced by the finite-mode bridge is itself the
zero velocity with the zero pressure slice.  Thus this branch of the repaired
BKM premise is explicitly a zero-flow cancellation artifact. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hWitness :
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            ((twoModeSchwartzDivergenceFreeInitialVelocity
              (a 0) (a 0) f (-f) hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    exact
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
        (a := a)
        (b := a)
        (f := f)
        (g := -f)
        (A := A)
        (B := A)
        (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
        (ν := ν)
        (T := T)
        ha
        ha
        hp
        hν
        haBound
        haBound
        hfDiv
        hgDiv
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
          a ν f)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hWitness
  rcases hWitness with ⟨W, hWvel, hWpress⟩
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a a f (-f) A A T haBound haBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWzero, hWpress, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- Exact BKM-data audit for the equal-amplitude anti-profile branch: the
finite-time witness can be chosen with zero velocity, zero pressure, the zero
vorticity envelope, and zero integral budget.  Thus no nontrivial BKM content
is hidden in this cancellation baseline. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
        ha A hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  refine ⟨W, hWzero, hWpress, ?_, integrableVorticityEnvelopeOn_zero T⟩
  simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Canonical-witness form of the equal-amplitude anti-profile audit.  The
finite-mode bridge does not merely produce some zero-flow witness: its output
is propositionally equal to the canonical zero finite-time witness, equipped
with the zero BKM envelope and zero integral budget. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_canonicalZeroWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W = zeroFiniteTimeRegularityWitness ν T ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
        ha A hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, hEnv, hInt⟩
  have hWcanon : W = zeroFiniteTimeRegularityWitness ν T := by
    have hvel : W.velocity = (zeroFiniteTimeRegularityWitness ν T).velocity := by
      simpa [zeroFiniteTimeRegularityWitness] using hWzero
    have hpress : W.pressure = (zeroFiniteTimeRegularityWitness ν T).pressure := by
      simpa [zeroFiniteTimeRegularityWitness] using hWpress
    cases W
    cases hvel
    cases hpress
    simp [zeroFiniteTimeRegularityWitness]
    constructor <;> rfl
  exact ⟨W, hWcanon, hWzero, hWpress, hEnv, hInt⟩

/-- Time-only pressure-gauge audit for the equal-amplitude anti-profile branch.
Allowing a nonzero time-dependent pressure gauge in the affine-plus-Schwartz
pressure class still produces only zero velocity, the stated gauge pressure,
the zero vorticity envelope, and zero integral budget. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hWitness :
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            ((twoModeSchwartzDivergenceFreeInitialVelocity
              (a 0) (a 0) f (-f) hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q := by
    exact
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        (a := a)
        (b := a)
        (f := f)
        (g := -f)
        (A := A)
        (B := A)
        (c := fun _ : NSTime => 0)
        (π := π)
        (ρ := fun _ : NSTime => 0)
        (q := q)
        (ν := ν)
        (T := T)
        ha
        ha
        contDiff_const
        hπ
        contDiff_const
        hν
        haBound
        haBound
        hfDiv
        hgDiv
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineTimeOnlyPressure
          a ν π f q)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hWitness
  rcases hWitness with ⟨W, hWvel, hWpress⟩
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  refine ⟨W, hWzero, hWpress, ?_, integrableVorticityEnvelopeOn_zero T⟩
  simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Canonical gauge-witness form of the time-only pressure audit.  The
equal-amplitude anti-profile bridge with a time-only affine-plus-Schwartz
pressure gauge is propositionally the canonical zero finite-time witness after
adding that same smooth time-only pressure gauge. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_canonicalGaugeWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W = (zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
        ha A π hπ q hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, hEnv, hInt⟩
  have hWcanon :
      W = (zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ := by
    have hvel :
        W.velocity =
          ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).velocity := by
      simpa [ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
        ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
        zeroFiniteTimeRegularityWitness] using hWzero
    have hpress :
        W.pressure =
          ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).pressure := by
      calc
        W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q := hWpress
        _ = ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).pressure := by
          funext t x
          simp [affineAddScalarSchwartzPressure,
            ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
            ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
            zeroFiniteTimeRegularityWitness]
    cases W
    cases hvel
    cases hpress
    simp [ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
      ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
      zeroFiniteTimeRegularityWitness]
    rfl
  exact ⟨W, hWcanon, hWzero, hWpress, hEnv, hInt⟩

/-- BKM-data form of the zero-flow initial-data classification.  If a
finite-time witness is zero velocity after packaging it with a BKM envelope and
integral budget, then the initial velocity data must itself be zero. -/
theorem BKMData_zeroVelocity_implies_initialVelocity_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 := by
  rcases hData with ⟨W, hWzero, _hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  funext x
  have hinit := W.initial_condition x
  rw [hWzero] at hinit
  simpa using hinit.symm

/-- BKM-layer form of the zero-flow initial-data obstruction.  A nonzero
initial velocity cannot be paired with zero velocity by adding BKM envelope
data. -/
theorem not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  exact hu0 (BKMData_zeroVelocity_implies_initialVelocity_zero hData)

/-- BKM-data form of the zero-flow pressure classification.  If a finite-time
witness is zero velocity after packaging it with a BKM envelope and integral
budget, then its pressure has zero spatial gradient throughout the certified
slab. -/
theorem BKMData_zeroVelocity_implies_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rcases hData with ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  intro t x ht0 htT
  have hmom := W.momentum_equation_on t x ht0 htT
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [hWzero, hWpress, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap] using hmom

/-- Combined BKM-data classification for the zero-flow branch.  Such a package
can only be attached to zero initial velocity data and pressure with zero
spatial gradient throughout the certified slab. -/
theorem BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 ∧
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ⟨BKMData_zeroVelocity_implies_initialVelocity_zero hData,
      BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData⟩

/-- Exact zero-flow BKM-data classification.  For a smooth pressure field, a
zero-velocity BKM package exists exactly when the initial data are zero and the
pressure has zero spatial gradient throughout the certified slab.  Thus the
BKM envelope and integral-budget layer adds no extra escape hatch to the
finite-time zero-flow witness surface. -/
theorem BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · intro hData
    exact
      BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
        hData
  · rintro ⟨hu0, hgrad⟩
    subst hu0
    rcases
        (zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) p hp).2 hgrad with
      ⟨W, hWzero, hWpress⟩
    refine
      ⟨W, hWzero, hWpress, (fun _ : NSTime => 0), 0, ?_,
        integrableVorticityEnvelopeOn_zero T⟩
    simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Time-only pressure is the exact surviving zero-flow BKM gauge.  For every
smooth time-only pressure, zero-velocity BKM data exists exactly for zero
initial velocity data. -/
theorem BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 := by
  constructor
  · intro hData
    exact
      ((BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := fun t : NSTime => fun _ : NSSpace => π t)
        (smoothSpaceTimePressure_timeOnly hπ)).1 hData).1
  · intro hu0
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := fun t : NSTime => fun _ : NSSpace => π t)
        (smoothSpaceTimePressure_timeOnly hπ)).2
        ⟨hu0, by
          intro t x _ht0 _htT
          exact spatialPressureGradient_timeOnly π t x⟩

/-- Positive BKM-data witness for the zero-flow branch with arbitrary smooth
time-only pressure.  This is the constructive half of the exact time-gauge
classification. -/
theorem BKMData_zeroVelocity_timeOnlyPressure
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      π hπ).2 rfl

/-- Nonzero initial data remain impossible even for the surviving time-only
pressure gauge. -/
theorem not_exists_BKMData_zeroVelocity_timeOnlyPressure_of_initialVelocity_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  exact hu0
    ((BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      (ν := ν) (T := T) (u0 := u0) π hπ).1 hData)

/-- BKM-layer form of the zero-flow pressure-gradient obstruction.  Even after
adding a vorticity envelope and an integral budget, a zero-flow finite-time
witness cannot carry any pressure field with a nonzero spatial gradient on the
certified slab. -/
theorem not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases hfail with ⟨t, x, ht0, htT, hgrad⟩
  exact hgrad
    (BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData t x ht0 htT)

/-- Combined BKM-layer zero-flow obstruction.  A proposed zero-velocity BKM
package is impossible as soon as either its initial velocity is nonzero or its
pressure has a nonzero spatial gradient somewhere on the certified slab. -/
theorem not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero_or_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
        hData with
    ⟨hu0zero, hgradzero⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hgrad =>
      rcases hgrad with ⟨t, x, ht0, htT, hne⟩
      exact hne (hgradzero t x ht0 htT)

/-- Exact zero-flow BKM-data classification for the spatial-affine pressure
subclass.  A pressure of the form `⟪c t, x⟫ + π t` can appear in a zero-flow
BKM package exactly when the initial velocity is zero and the affine
coefficient `c` vanishes throughout the certified slab. -/
theorem BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧ ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  have hp :
      smoothSpaceTimePressure
        (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure
      hc hπ (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ))) q
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
          (ν := ν)
          (T := T)
          (u0 := u0)
          (p := affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q)
          hp).1 hData with
      ⟨hu0, hgrad⟩
    refine ⟨hu0, ?_⟩
    intro t ht0 htT
    simpa [spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
      c π q t (0 : NSSpace)] using hgrad t (0 : NSSpace) ht0 htT
  · rintro ⟨hu0, hczero⟩
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q)
        hp).2
        ⟨hu0, by
          intro t x ht0 htT
          simpa [spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
            c π q t x] using hczero t ht0 htT⟩

/-- Constructive zero-flow BKM data for the spatial-affine pressure subclass
when the affine coefficient vanishes on the certified slab. -/
theorem BKMData_zeroVelocity_spatialAffinePressure_of_affineCoeff_zeroOn
    {ν T : ℝ}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π)
    (hczero : ∀ t, 0 ≤ t → t ≤ T → c t = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      c π q hc hπ).2
      ⟨rfl, hczero⟩

/-- Combined spatial-affine zero-flow obstruction.  A proposed zero-velocity
BKM package in this pressure subclass is impossible as soon as either the
initial velocity is nonzero or the affine pressure coefficient is nonzero at
one certified slab time. -/
theorem not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_initialVelocity_ne_zero_or_exists_nonzeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π)
    (hfail :
      u0 ≠ 0 ∨ ∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
        (ν := ν) (T := T) (u0 := u0) c π q hc hπ).1 hData with
    ⟨hu0zero, hczero⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hcz =>
      rcases hcz with ⟨t, ht0, htT, hct⟩
      exact hct (hczero t ht0 htT)

/-- BKM-layer form of the spatial-affine pressure obstruction.  Even after
adding a vorticity envelope and an integral budget, a zero-flow finite-time
witness with pure spatial-affine pressure forces the affine pressure
coefficient to vanish on the certified slab. -/
theorem not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases hc with ⟨t, ht0, htT, hct⟩
  rcases hData with ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  exact hct
    (W.zeroVelocity_spatialAffinePressure_implies_zeroAffineCoeffOn
      c π q hWzero hWpress t ht0 htT)

/-- The spatial gradient of a time-scaled Schwartz pressure slice is the
time coefficient times the spatial gradient of the fixed Schwartz profile. -/
theorem spatialPressureGradient_scalarSchwartzPressure
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
      ρ t • spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  unfold spatialPressureGradient
  change gradient ((ρ t) • fun y : NSSpace => q y) x =
    ρ t • gradient (fun y : NSSpace => q y) x
  rw [gradient, fderiv_const_smul_field]
  simp [gradient]

/-- In the full affine-plus-localized pressure class, the zero-flow forcing
term is exactly the affine coefficient plus the time-scaled Schwartz spatial
gradient.  This is the algebraic boundary that any zero-flow repair must meet. -/
theorem spatialPressureGradient_affineAddScalarSchwartzPressure
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
      c t + ρ t •
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  have haff :
      DifferentiableAt ℝ
        (fun y : NSSpace => (fun s : NSTime => fun z : NSSpace => ⟪c s, z⟫ + π s) t y)
        x := by
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      (((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const
        (π t)).differentiableAt
  have hschwartz :
      DifferentiableAt ℝ
        (fun y : NSSpace => (fun s : NSTime => fun z : NSSpace => ρ s * q z) t y)
        x := by
    exact ((q.smooth'.differentiable (by simp)) x).const_mul (ρ t)
  rw [affineAddScalarSchwartzPressure]
  rw [spatialPressureGradient_add haff hschwartz]
  rw [spatialPressureGradient_affinePressure]
  rw [spatialPressureGradient_scalarSchwartzPressure]

/-- Two-point obstruction for the concrete affine-plus-localized pressure
repair of the non-cancelling constant-one two-mode branch.  Under inviscid
convection closure, the exact pressure-gradient repair condition forces the
viscous Laplacian residual pair-difference to be a scalar multiple of the
fixed Schwartz pressure-gradient pair-difference.  The arbitrary affine
coefficient and time-only gauge disappear after subtracting the two spatial
points. -/
theorem not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          ρ t •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hbad with ⟨t, x, y, hbad⟩
  let Lx :=
    spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
      spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x
  let Ly :=
    spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
      spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y
  let Qx := spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
  let Qy := spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
  have hbalance :=
    (momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
      ν (affineAddScalarSchwartzPressure c π ρ q) f g hclosure).1 hmom
  have hx :
      spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • Lx := by
    simpa [Lx] using hbalance t x
  have hy :
      spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y =
        (ν : ℝ) • Ly := by
    simpa [Ly] using hbalance t y
  have hpair :
      (ν : ℝ) • (Lx - Ly) = ρ t • (Qx - Qy) := by
    calc
      (ν : ℝ) • (Lx - Ly) = (ν : ℝ) • Lx - (ν : ℝ) • Ly := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y := by
        rw [← hx, ← hy]
      _ = (c t + ρ t • Qx) - (c t + ρ t • Qy) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y]
      _ = ρ t • Qx - ρ t • Qy := by
        abel
      _ = ρ t • (Qx - Qy) := by
        rw [smul_sub]
  exact hbad (by simpa [Lx, Ly, Qx, Qy] using hpair)

/-- If the localized pressure amplitude is zero at a time, the same
two-point obstruction reduces to spatial constancy of the viscous Laplacian
residual at that time.  For positive viscosity, a single residual
pair-difference blocks every affine-gauge repair with inactive localized
pressure at that time. -/
theorem not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_zeroLocalizedAmplitude_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        ρ t = 0 ∧
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure ?_
  rcases hbad with ⟨t, x, y, hρzero, hLne⟩
  refine ⟨t, x, y, ?_⟩
  intro hpair
  have hsmul :
      (ν : ℝ) •
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) = 0 := by
    simpa [hρzero] using hpair
  have hdiff :
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hν.ne'
  exact hLne (sub_eq_zero.mp hdiff)

/-- Scalar-amplitude obstruction for the concrete affine-plus-localized
pressure repair.  If, at one time, no scalar can make the fixed Schwartz
pressure-gradient pair-differences match the viscous Laplacian residual
pair-differences, then there is no choice of affine coefficient, time-only
gauge, or localized amplitude curve that repairs the non-cancelling
constant-one branch. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t, ∀ r : ℝ, ∃ x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          r •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  rintro ⟨c, π, ρ, hmom⟩
  rcases hbad with ⟨t, hbad_t⟩
  rcases hbad_t (ρ t) with ⟨x, y, hpair⟩
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure ⟨t, x, y, hpair⟩ hmom

/-- Two-pair scalar-amplitude obstruction for the concrete
affine-plus-localized pressure repair.  If two spatial pairs at the same time
have the same fixed Schwartz pressure-gradient pair-difference but different
viscous Laplacian residual pair-differences, then no single localized amplitude
can fit both pairs; hence no affine coefficient, gauge, or amplitude curve
repairs the non-cancelling constant-one branch. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
        ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  classical
  refine
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure ?_
  rcases hbad with ⟨t, x₁, y₁, x₂, y₂, hQeq, hLne⟩
  let L₁ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)
  let L₂ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂)
  let Q₁ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁
  let Q₂ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂
  have hQeq' : Q₁ = Q₂ := by
    simpa [Q₁, Q₂] using hQeq
  have hLne' : L₁ ≠ L₂ := by
    simpa [L₁, L₂] using hLne
  refine ⟨t, fun r => ?_⟩
  by_cases hfirst : (ν : ℝ) • L₁ ≠ r • Q₁
  · exact ⟨x₁, y₁, by simpa [L₁, Q₁] using hfirst⟩
  · refine ⟨x₂, y₂, ?_⟩
    intro hsecond
    have hfirst_eq : (ν : ℝ) • L₁ = r • Q₁ := not_not.mp hfirst
    have hsecond_eq : (ν : ℝ) • L₂ = r • Q₂ := by
      simpa [L₂, Q₂] using hsecond
    have hsmul_eq : (ν : ℝ) • L₁ = (ν : ℝ) • L₂ := by
      calc
        (ν : ℝ) • L₁ = r • Q₁ := hfirst_eq
        _ = r • Q₂ := by rw [hQeq']
        _ = (ν : ℝ) • L₂ := hsecond_eq.symm
    have hsmul_zero : (ν : ℝ) • (L₁ - L₂) = 0 := by
      rw [smul_sub, hsmul_eq, sub_self]
    have hdiff_zero : L₁ - L₂ = 0 :=
      (smul_eq_zero.mp hsmul_zero).resolve_left hν.ne'
    exact hLne' (sub_eq_zero.mp hdiff_zero)

/-- If the fixed Schwartz pressure profile has the same spatial gradient at a
pair of points while the viscous Laplacian residual separates those points,
then no scalar localized amplitude can repair the non-cancelling constant-one
branch.  This blocks the full affine-plus-localized pressure family, not just a
preselected amplitude curve. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_pressureGradient_pair_eq_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y ∧
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure ?_
  rcases hbad with ⟨t, x, y, hQeq, hLne⟩
  refine ⟨t, fun r => ⟨x, y, ?_⟩⟩
  intro hpair
  have hsmul :
      (ν : ℝ) •
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) = 0 := by
    simpa [hQeq] using hpair
  have hdiff :
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hν.ne'
  exact hLne (sub_eq_zero.mp hdiff)

/-- BKM-data-level form of the two-pair over-determination obstruction.  If
the bad pair time lies inside the certified slab, then no finite-time witness
can hide the failed positive-viscosity repair inside its BKM envelope: the
witness momentum equation at the four slab points already forces the two
Laplacian residual pair-differences to agree. -/
theorem not_exists_BKMData_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∃ W : ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  rintro ⟨c, π, ρ, W, hWvel, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  rcases hbad with ⟨t, x₁, y₁, x₂, y₂, ht0, htT, hQeq, hLne⟩
  let L₁ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)
  let L₂ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂)
  let Q₁ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁
  let Q₂ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂
  have hQeq' : Q₁ = Q₂ := by
    simpa [Q₁, Q₂] using hQeq
  have hLne' : L₁ ≠ L₂ := by
    simpa [L₁, L₂] using hLne
  have hpressure :
      ∀ x : NSSpace,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
    intro x
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at hmom
    simpa [hclosure t x] using hmom
  have hpair₁ : (ν : ℝ) • L₁ = ρ t • Q₁ := by
    calc
      (ν : ℝ) • L₁ =
          (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁) := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x₁ -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y₁ := by
        rw [← hpressure x₁, ← hpressure y₁]
      _ = (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁) -
            (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x₁,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y₁]
      _ = ρ t • Q₁ := by
        rw [smul_sub]
        abel
  have hpair₂ : (ν : ℝ) • L₂ = ρ t • Q₂ := by
    calc
      (ν : ℝ) • L₂ =
          (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂) := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x₂ -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y₂ := by
        rw [← hpressure x₂, ← hpressure y₂]
      _ = (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂) -
            (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x₂,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y₂]
      _ = ρ t • Q₂ := by
        rw [smul_sub]
        abel
  have hsmul_eq : (ν : ℝ) • L₁ = (ν : ℝ) • L₂ := by
    calc
      (ν : ℝ) • L₁ = ρ t • Q₁ := hpair₁
      _ = ρ t • Q₂ := by rw [hQeq']
      _ = (ν : ℝ) • L₂ := hpair₂.symm
  have hsmul_zero : (ν : ℝ) • (L₁ - L₂) = 0 := by
    rw [smul_sub, hsmul_eq, sub_self]
  have hdiff_zero : L₁ - L₂ = 0 :=
    (smul_eq_zero.mp hsmul_zero).resolve_left hν.ne'
  exact hLne' (sub_eq_zero.mp hdiff_zero)

/-- Route-level composition for the non-cancelling constant-one two-mode
branch.  The inviscid branch supplies a nonzero finite-time BKM-premise
package, but the same profile pair cannot be promoted to a positive-viscosity
finite-time BKM datum through any affine-plus-one-Schwartz-pressure repair
when the two-pair over-determination witness is present on the certified slab.
-/
theorem oneOneTwoModeSchwartzVelocity_inviscidBKM_and_not_exists_posViscosity_BKMData_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ((∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
        ∃ W : ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · exact
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure
  · exact
      not_exists_BKMData_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
        hν f g q hclosure hbad

/-- A Schwartz pressure profile on the concrete Navier--Stokes space cannot
have a nonzero globally constant spatial gradient.  Boundedness of the
Schwartz function contradicts the affine growth forced by a nonzero constant
gradient. -/
theorem schwartzMap_gradient_constant_eq_zero
    (q : 𝓢(NSSpace, ℝ))
    (hconst : ∀ x : NSSpace,
      gradient (fun z : NSSpace => q z) x =
        gradient (fun z : NSSpace => q z) (0 : NSSpace)) :
    ∀ x : NSSpace, gradient (fun z : NSSpace => q z) x = 0 := by
  let f : NSSpace → ℝ := fun z => q z
  let g : NSSpace := gradient f (0 : NSSpace)
  have hdiff : Differentiable ℝ f := by
    simpa [f] using q.smooth'.differentiable (by simp)
  have hgzero : g = 0 := by
    by_contra hg
    let φ : NSSpace →L[ℝ] ℝ := fderiv ℝ f (0 : NSSpace)
    have hfd : ∀ z : NSSpace, fderiv ℝ f z = φ := by
      intro z
      apply ContinuousLinearMap.ext
      intro v
      have hz : DifferentiableAt ℝ f z := hdiff z
      have h0 : DifferentiableAt ℝ f (0 : NSSpace) := hdiff 0
      have hgradz : gradient f z = gradient f (0 : NSSpace) := by
        simpa [f] using hconst z
      calc
        (fderiv ℝ f z) v = ⟪gradient f z, v⟫ := by
          rw [← inner_gradient_left hz]
        _ = ⟪g, v⟫ := by
          simpa [g] using congrArg (fun w : NSSpace => ⟪w, v⟫) hgradz
        _ = (fderiv ℝ f (0 : NSSpace)) v := by
          rw [inner_gradient_left h0]
        _ = φ v := rfl
    let M : ℝ := (SchwartzMap.seminorm ℝ 0 0) q
    have hMnonneg : 0 ≤ M :=
      apply_nonneg (SchwartzMap.seminorm ℝ 0 0) q
    have hnormgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hdenpos : 0 < ‖g‖ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hnormgpos)
    have hdenne : ‖g‖ ^ 2 ≠ 0 := ne_of_gt hdenpos
    let r : ℝ := (2 * M + 1) / ‖g‖ ^ 2
    have hrmul : r * ‖g‖ ^ 2 = 2 * M + 1 := by
      simpa [r] using (div_mul_cancel₀ (2 * M + 1) hdenne)
    have hbound : ‖q (r • g) - q (0 : NSSpace)‖ ≤ 2 * M := by
      calc
        ‖q (r • g) - q (0 : NSSpace)‖ ≤
            ‖q (r • g)‖ + ‖q (0 : NSSpace)‖ :=
          norm_sub_le _ _
        _ ≤ M + M := by
          exact add_le_add (SchwartzMap.norm_le_seminorm ℝ q (r • g))
            (SchwartzMap.norm_le_seminorm ℝ q (0 : NSSpace))
        _ = 2 * M := by ring
    have haffnorm : ‖q (r • g) - q (0 : NSSpace) - φ ((r • g) - 0)‖ ≤ 0 := by
      simpa [f, zero_mul] using
        ((convex_univ : Convex ℝ (Set.univ : Set NSSpace)).norm_image_sub_le_of_norm_fderiv_le'
          (f := f)
          (C := 0)
          (s := Set.univ)
          (x := (0 : NSSpace))
          (y := r • g)
          (φ := φ)
          (fun z _hz => hdiff z)
          (fun z _hz => by rw [hfd z, sub_self, norm_zero])
          trivial
          trivial)
    have haffzero : q (r • g) - q (0 : NSSpace) - φ ((r • g) - 0) = 0 := by
      exact norm_eq_zero.mp (le_antisymm haffnorm (norm_nonneg _))
    have hdiff_eq : q (r • g) - q (0 : NSSpace) = φ ((r • g) - 0) := by
      linarith
    have hφg : φ g = ‖g‖ ^ 2 := by
      have h0 : DifferentiableAt ℝ f (0 : NSSpace) := hdiff 0
      calc
        φ g = ⟪gradient f (0 : NSSpace), g⟫ := by
          rw [inner_gradient_left h0]
        _ = ⟪g, g⟫ := rfl
        _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    have hphi : φ ((r • g) - 0) = r * ‖g‖ ^ 2 := by
      calc
        φ ((r • g) - 0) = φ (r • g) := by simp
        _ = r * φ g := by simp
        _ = r * ‖g‖ ^ 2 := by rw [hφg]
    have hdiff_val : q (r • g) - q (0 : NSSpace) = 2 * M + 1 := by
      rw [hdiff_eq, hphi, hrmul]
    have hnorm_eq : ‖q (r • g) - q (0 : NSSpace)‖ = 2 * M + 1 := by
      rw [hdiff_val, Real.norm_of_nonneg]
      linarith
    have : 2 * M + 1 ≤ 2 * M := by
      rwa [hnorm_eq] at hbound
    linarith
  intro x
  simpa [f, g, hgzero] using hconst x

/-- Exact zero-flow BKM-data classification for the full
affine-plus-localized pressure class.  The localized pressure term leaves no
extra gauge freedom: zero-flow BKM data exists exactly when the initial
velocity is zero and the affine coefficient cancels the time-scaled Schwartz
pressure gradient at every point of the certified slab. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
  have hp : smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
          (ν := ν)
          (T := T)
          (u0 := u0)
          (p := affineAddScalarSchwartzPressure c π ρ q)
          hp).1 hData with
      ⟨hu0, hgrad⟩
    refine ⟨hu0, ?_⟩
    intro t x ht0 htT
    simpa [spatialPressureGradient_affineAddScalarSchwartzPressure
      c π ρ q t x] using hgrad t x ht0 htT
  · rintro ⟨hu0, hbalance⟩
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν)
        (T := T)
        (u0 := u0)
        (p := affineAddScalarSchwartzPressure c π ρ q)
        hp).2
        ⟨hu0, by
          intro t x ht0 htT
          simpa [spatialPressureGradient_affineAddScalarSchwartzPressure
            c π ρ q t x] using hbalance t x ht0 htT⟩

/-- Constructive zero-flow BKM data for the full affine-plus-localized pressure
class when the pressure-gradient balance holds on the certified slab. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_pressureGradientBalanceOn
    {ν T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbalance :
      ∀ t x, 0 ≤ t → t ≤ T →
        c t + ρ t •
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
      (ν := ν)
      (T := T)
      (u0 := (0 : NSInitialVelocity))
      c π ρ q hc hπ hρ).2
      ⟨rfl, hbalance⟩

/-- Combined no-go for the full affine-plus-localized pressure class.  Zero
velocity BKM data is impossible if the initial velocity is nonzero or if the
affine-plus-localized pressure-gradient balance fails at one certified slab
point. -/
theorem not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_pressureGradientBalanceFailureOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨hu0zero, hbalance⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hbad =>
      rcases hbad with ⟨t, x, ht0, htT, hneq⟩
      exact hneq (hbalance t x ht0 htT)

/-- A localized Schwartz pressure profile with two different spatial gradients
at a time where its amplitude is nonzero cannot be hidden by choosing an
affine pressure coefficient.  This blocks the main cancellation repair for
zero-flow BKM data in the full affine-plus-localized pressure subclass. -/
theorem not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_nonconstant_schwartzPressureGradientOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, ∃ y, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0 ∧
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x ≠
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  intro hData
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨hu0zero, hbalance⟩
  cases hfail with
  | inl hu0 =>
      exact hu0 hu0zero
  | inr hnonconstant =>
      rcases hnonconstant with ⟨t, x, y, ht0, htT, hρne, hgradne⟩
      let gx :=
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
      let gy :=
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
      have hx : c t + ρ t • gx = 0 := hbalance t x ht0 htT
      have hy : c t + ρ t • gy = 0 := hbalance t y ht0 htT
      have hsmul : ρ t • (gx - gy) = 0 := by
        calc
          ρ t • (gx - gy) = (c t + ρ t • gx) - (c t + ρ t • gy) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          _ = 0 := by
            rw [hx, hy]
            simp
      rcases smul_eq_zero.mp hsmul with hρzero | hdiff
      · exact hρne hρzero
      · exact hgradne (sub_eq_zero.mp hdiff)

/-- Any full affine-plus-localized zero-flow BKM data with nonzero localized
amplitude at a certified slab time forces the fixed Schwartz pressure profile
to have spatially constant gradient at that time.  This is the exact repair
burden left by the affine cancellation freedom. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y := by
  intro t ht0 htT hρne x y
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨_hu0zero, hbalance⟩
  let gx :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
  let gy :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
  have hx : c t + ρ t • gx = 0 := hbalance t x ht0 htT
  have hy : c t + ρ t • gy = 0 := hbalance t y ht0 htT
  have hsmul : ρ t • (gx - gy) = 0 := by
    calc
      ρ t • (gx - gy) = (c t + ρ t • gx) - (c t + ρ t • gy) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = 0 := by
        rw [hx, hy]
        simp
  rcases smul_eq_zero.mp hsmul with hρzero | hdiff
  · exact False.elim (hρne hρzero)
  · exact sub_eq_zero.mp hdiff

/-- The constant-gradient consequence is even sharper for Schwartz profiles:
at any nonzero-amplitude certified slab time, a full affine-plus-localized
zero-flow BKM datum forces the localized pressure profile's spatial gradient
to vanish everywhere. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x = 0 := by
  intro t ht0 htT hρne
  have hconst :=
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData t ht0 htT hρne
  have hconstGradient :
      ∀ x : NSSpace,
        gradient (fun z : NSSpace => q z) x =
          gradient (fun z : NSSpace => q z) (0 : NSSpace) := by
    intro x
    simpa [spatialPressureGradient] using hconst x (0 : NSSpace)
  have hzero := schwartzMap_gradient_constant_eq_zero q hconstGradient
  intro x
  simpa [spatialPressureGradient] using hzero x

/-- Therefore a nonzero-amplitude zero-flow BKM datum in the full
affine-plus-localized pressure class also forces the affine pressure
coefficient to vanish at that certified slab time. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 → c t = 0 := by
  intro t ht0 htT hρne
  rcases
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
    ⟨_hu0zero, hbalance⟩
  have hgradzero :=
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData t ht0 htT hρne (0 : NSSpace)
  have hbal : c t + ρ t • (0 : NSSpace) = 0 := by
    simpa [hgradzero] using hbalance t (0 : NSSpace) ht0 htT
  simpa using hbal

/-- Exact zero-flow BKM-data classification after the Schwartz constant-gradient
collapse.  The full affine-plus-localized pressure repair can support zero
velocity only when the initial velocity is zero, the affine spatial coefficient
vanishes throughout the certified slab, and any certified nonzero localized
amplitude forces the whole fixed Schwartz pressure gradient to vanish. -/
theorem BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
          (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).1 hData with
      ⟨hu0zero, hbalance⟩
    refine ⟨hu0zero, ?_, ?_⟩
    · intro t ht0 htT
      by_cases hρzero : ρ t = 0
      · have hbal0 : c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t
              (0 : NSSpace) = 0 :=
          hbalance t (0 : NSSpace) ht0 htT
        simpa [hρzero] using hbal0
      · exact
          BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
            c π ρ q hc hπ hρ hData t ht0 htT hρzero
    · rintro ⟨t, ht0, htT, hρne⟩ s x
      have hzeroAt :=
        BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
          c π ρ q hc hπ hρ hData t ht0 htT hρne x
      simpa [spatialPressureGradient] using hzeroAt
  · rintro ⟨hu0zero, hcZero, hgradZeroOfNonzeroAmplitude⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
        (ν := ν) (T := T) (u0 := u0) c π ρ q hc hπ hρ).2
        ⟨hu0zero, by
          intro t x ht0 htT
          by_cases hρzero : ρ t = 0
          · simp [hcZero t ht0 htT, hρzero]
          · have hgradZero :=
              hgradZeroOfNonzeroAmplitude ⟨t, ht0, htT, hρzero⟩ t x
            simp [hcZero t ht0 htT, hgradZero]⟩

/-- Arbitrary-pressure momentum-equation classification for the
equal-amplitude anti-profile branch.  Since the velocity is identically zero,
the full pointwise momentum equation holds exactly when the pressure has zero
spatial gradient everywhere. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · intro hME t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap] using hME t x
  · intro hgrad t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap, hgrad t x]

/-- Finite-time witness classification for the cancelled equal-amplitude
anti-profile branch with an arbitrary smooth pressure.  Once the actual
finite-time witness structure is required to use the cancelled two-mode
velocity and the given pressure, its built-in slabwise momentum equation is
equivalent to vanishing spatial pressure gradient on the certified slab. -/
theorem exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simpa [hWvel, hWpress, hvel, timeVelocityDerivative_zero,
      spatialConvection_zero, hlap] using W.momentum_equation_on t x ht0 htT
  · intro hgrad
    let W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T :=
      { velocity := twoModeSchwartzVelocity a a f (-f)
        pressure := p
        smooth_velocity := by
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).smooth_velocity
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
            equalAmplitudeAntiProfileSchwartzVelocity_zero a f
          have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
            simpa [constantVelocityField] using
              spatialLaplacian_constantVelocityField (0 : NSSpace) t x
          simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap,
            hgrad t x ht0 htT]
        incompressible_on := by
          intro t x ht0 htT
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            spatialDivergence_zero t x
        initial_condition := by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f,
            equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).initial_condition
        bounded_energy_on := by
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).bounded_energy_on }
    exact ⟨W, rfl, rfl⟩

/-- Internal-pressure witness obstruction for the cancelled equal-amplitude
anti-profile branch.  If a finite-time witness itself uses the cancelled
two-mode velocity, then its own pressure field has zero spatial gradient on
the certified slab.  This closes the variant where the pressure is not fixed in
advance but is carried hidden inside the witness record. -/
theorem ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient W.pressure t x = 0 := by
  intro t x ht0 htT
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [hWvel, hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap]
    using W.momentum_equation_on t x ht0 htT

/-- Same-witness BKM envelope for the cancelled equal-amplitude anti-profile
branch.  If an actual finite-time witness uses the cancelled two-mode velocity,
then its vorticity envelope can be chosen to be identically zero with zero
integral budget.  Thus the BKM packaging adds no further analytic burden on
this branch once the witness velocity is fixed. -/
theorem ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    simpa [hvel] using hWvel
  exact
    ⟨by simpa [hWzero] using vorticityEnvelopeOn_zero T,
      integrableVorticityEnvelopeOn_zero T⟩

/-- Internal-pressure no-go for the cancelled equal-amplitude anti-profile
branch.  There is no finite-time witness whose velocity is the cancelled
two-mode field and whose own stored pressure has a nonzero spatial-gradient
point inside the certified slab. -/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_of_exists_pressure_spatialPressureGradient_ne_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient W.pressure t x ≠ 0 := by
  rintro ⟨W, hWvel, t, x, ht0, htT, hgrad_ne⟩
  exact hgrad_ne
    (ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
      a f W hWvel t x ht0 htT)

/-- Witness-level arbitrary-pressure no-go for the cancelled equal-amplitude
anti-profile branch.  A single nonzero pressure-gradient point inside the
certified slab rules out any finite-time witness whose velocity is the
cancelled two-mode field and whose pressure is the proposed arbitrary pressure.
-/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hbad :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p := by
  rintro ⟨W, hWvel, hWpress⟩
  rcases hbad with ⟨t, x, ht0, htT, hgrad_ne⟩
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  exact hgrad_ne
    (by
      simpa [hWvel, hWpress, hvel, timeVelocityDerivative_zero,
        spatialConvection_zero, hlap] using W.momentum_equation_on t x ht0 htT)

/-- Momentum-equation classification for the equal-amplitude anti-profile
branch with the full affine-plus-localized Schwartz pressure class.  Since the
velocity is identically zero, the full pointwise momentum equation can hold
only in the same collapsed pressure cases as the zero-flow BKM classification:
the affine spatial coefficient is zero for every time, and any nonzero
localized amplitude forces the fixed Schwartz pressure gradient to vanish
everywhere. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      (∀ t, c t = 0) ∧
        ((∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · intro hME
    have hbalance :
        ∀ t x,
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
      intro t x
      have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
        equalAmplitudeAntiProfileSchwartzVelocity_zero a f
      have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
        simpa [constantVelocityField] using
          spatialLaplacian_constantVelocityField (0 : NSSpace) t x
      simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap,
        spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x]
        using hME t x
    have hgradZeroOfNonzero :
        (∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0 := by
      rintro ⟨t0, hρne⟩ s x
      let g0 :=
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t0
          (0 : NSSpace)
      have hconstGradient :
          ∀ x : NSSpace,
            gradient (fun y : NSSpace => q y) x =
              gradient (fun y : NSSpace => q y) (0 : NSSpace) := by
        intro x
        let gx :=
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t0 x
        have hx : c t0 + ρ t0 • gx = 0 := hbalance t0 x
        have h0 : c t0 + ρ t0 • g0 = 0 := hbalance t0 (0 : NSSpace)
        have hsmul : ρ t0 • (gx - g0) = 0 := by
          calc
            ρ t0 • (gx - g0) = (c t0 + ρ t0 • gx) - (c t0 + ρ t0 • g0) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            _ = 0 := by
              rw [hx, h0]
              simp
        rcases smul_eq_zero.mp hsmul with hρzero | hdiff
        · exact False.elim (hρne hρzero)
        · simpa [gx, g0, spatialPressureGradient] using sub_eq_zero.mp hdiff
      have hzero := schwartzMap_gradient_constant_eq_zero q hconstGradient
      simpa [spatialPressureGradient] using hzero x
    refine ⟨?_, hgradZeroOfNonzero⟩
    intro t
    by_cases hρzero : ρ t = 0
    · have hbal0 := hbalance t (0 : NSSpace)
      simpa [hρzero] using hbal0
    · have hgradZero := hgradZeroOfNonzero ⟨t, hρzero⟩ t (0 : NSSpace)
      have hbal0 := hbalance t (0 : NSSpace)
      simpa [hgradZero] using hbal0
  · rintro ⟨hcZero, hgradZeroOfNonzero⟩ t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    have hpress :
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x = 0 := by
      rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x]
      by_cases hρzero : ρ t = 0
      · simp [hcZero t, hρzero]
      · have hgradZero := hgradZeroOfNonzero ⟨t, hρzero⟩ t x
        simp [hcZero t, hgradZero]
    simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap, hpress]

/-- Abstract BKM-data normalization for the equal-amplitude anti-profile
velocity over zero initial data.  The cancelled two-mode velocity carries
exactly the same BKM-data packages as the zero velocity, for any pressure
field. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · rintro ⟨W, hWvel, hWpress, Ω, Bint, hEnv, hInt⟩
    refine ⟨W, ?_, hWpress, Ω, Bint, hEnv, hInt⟩
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  · rintro ⟨W, hWzero, hWpress, Ω, Bint, hEnv, hInt⟩
    refine ⟨W, ?_, hWpress, Ω, Bint, hEnv, hInt⟩
    calc
      W.velocity = (0 : NSVelocityField) := hWzero
      _ = twoModeSchwartzVelocity a a f (-f) :=
        (equalAmplitudeAntiProfileSchwartzVelocity_zero a f).symm

/-- Abstract BKM-data normalization over the syntactic equal-amplitude
anti-profile initial datum.  After both the initial slice and velocity cancel,
this witness surface is exactly the zero-initial, zero-velocity BKM-data
surface for the same pressure field. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  rw [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f]
  exact BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p

/-- Exact zero-budget normal form for BKM data over the syntactic
equal-amplitude anti-profile initial datum.  On this cancelled branch, allowing
an arbitrary BKM envelope and integral budget is equivalent to using the same
finite-time witness with the identically zero envelope and zero budget. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVorticityEnvelope_zeroBudget
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
    rcases
        ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
          a f W hWvel with
      ⟨hZeroEnv, hZeroInt⟩
    exact ⟨W, hWvel, hWpress, hZeroEnv, hZeroInt⟩
  · rintro ⟨W, hWvel, hWpress, hZeroEnv, hZeroInt⟩
    exact ⟨W, hWvel, hWpress, (fun _ : NSTime => 0), 0, hZeroEnv, hZeroInt⟩

/-- Exact arbitrary-pressure BKM-data classification for the cancelled
equal-amplitude anti-profile velocity over zero initial data.  For a smooth
pressure field, the only surviving pressure information is the zero spatial
gradient condition on the certified slab. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rw [BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p]
  constructor
  · intro hData
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).1 hData |>.2
  · intro hgrad
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).2
        ⟨rfl, hgrad⟩

/-- Exact arbitrary-pressure BKM-data classification over the syntactic
equal-amplitude anti-profile initial datum.  The cancelled initial slice and
velocity reduce the package to the same pressure-gradient boundary as the
zero-flow branch. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  rw [BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity a f p]
  constructor
  · intro hData
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).1 hData |>.2
  · intro hgrad
    exact
      (BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) hp).2
        ⟨rfl, hgrad⟩

/-- Arbitrary-pressure no-go for BKM data on the cancelled equal-amplitude
anti-profile velocity.  Any nonzero pressure gradient on the certified slab
rules out the structured BKM-data package, independently of the pressure
ansatz. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  exact
    (not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) (p := p) hfail)
      ((BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
        a f p).1 hData)

/-- Arbitrary-pressure no-go over the syntactic anti-profile initial datum.
Changing the pressure family cannot repair the cancelled branch unless the
pressure is spatially constant on the certified slab. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  exact
    (not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity)) (p := p) hfail)
      ((BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
        a f p).1 hData)

/-- Clause/data separation for arbitrary pressure fields on the cancelled
equal-amplitude anti-profile branch.  The repaired finite-energy BKM clause is
inhabited at the zero datum, but any pressure with a nonzero spatial gradient
on the certified slab cannot be packaged as matching BKM data for the cancelled
two-mode velocity. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
      not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
        a f hfail⟩

/-- Syntactic initial-datum version of the arbitrary-pressure clause/data
separation.  A repaired finite-energy BKM clause remains available for the
cancelled anti-profile initial datum, but a pressure with nonzero slabwise
spatial gradient cannot be the matching BKM-data pressure. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · exact
      not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
        a f hfail

/-- Exact repaired-clause/BKM-data boundary for arbitrary smooth pressures on
the cancelled equal-amplitude anti-profile branch over zero initial data.  The
finite-energy BKM clause is always inhabited at the zero datum, so the
remaining obstruction to matching BKM data is precisely the spatial pressure
gradient on the certified slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        (ν := ν) (T := T) a f hp).1 hData
  · intro hgrad
    exact
      ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
        (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2 hgrad⟩

/-- Syntactic initial-datum version of the exact repaired-clause/BKM-data
boundary.  The equal-amplitude anti-profile initial datum reduces to zero, so
the combined clause-and-data package exists exactly when the pressure is
spatially constant on the certified slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
        (ν := ν) (T := T) a f hp).1 hData
  · intro hgrad
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2 hgrad⟩

/-- Arbitrary-pressure constructor-input separation for the repaired
finite-energy BKM clause over the syntactic anti-profile initial datum.  The
repaired clause is inhabited, but the pointwise momentum equation for the
cancelled anti-profile velocity is impossible for any pressure with a nonzero
spatial gradient. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro hME
    rcases hbad with ⟨t, x, hgrad⟩
    exact hgrad
      ((momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME t x)

/-- Exact arbitrary-pressure constructor-input boundary for the repaired
finite-energy BKM clause over the syntactic anti-profile initial datum.  Since
the repaired clause is inhabited after the anti-profile initial slice cancels,
the conjunction with the raw pointwise momentum equation is exactly the
zero-pressure-gradient condition. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, hME⟩
    exact
      (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME
  · intro hgrad
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          a ν f p).2 hgrad⟩

/-- Exact arbitrary-pressure clause/data/constructor boundary for the
cancelled equal-amplitude anti-profile branch.  Adding the BKM-data witness
does not weaken the raw constructor requirement: the repaired finite-energy
BKM clause, matching BKM data, and pointwise momentum equation coexist exactly
when the arbitrary pressure has zero spatial gradient everywhere. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨_hClause, _hData, hME⟩
    exact
      (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
        a ν f p).1 hME
  · intro hgrad
    refine ⟨?_, ?_, ?_⟩
    · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
        (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
    · exact
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
          (ν := ν) (T := T) a f hp).2
          (by
            intro t x _ht0 _htT
            exact hgrad t x)
    · exact
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
          a ν f p).2 hgrad

/-- BKM-data classification for the equal-amplitude anti-profile branch with
the full affine-plus-localized Schwartz pressure class.  Even after adding the
BKM witness and envelope layer, this branch is exactly the zero-flow pressure
classification: the affine coefficient vanishes on the certified slab, and any
nonzero localized amplitude on that slab forces the fixed Schwartz pressure
gradient to vanish everywhere. -/
theorem BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  rw [BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity
    a f (affineAddScalarSchwartzPressure c π ρ q)]
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
          c π ρ q hc hπ hρ).1 hData with
      ⟨_hInitial, hcZero, hgradZero⟩
    exact ⟨hcZero, hgradZero⟩
  · rintro ⟨hcZero, hgradZero⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
        c π ρ q hc hπ hρ).2
        ⟨rfl, hcZero, hgradZero⟩

/-- Same exact classification over the syntactic equal-amplitude anti-profile
initial datum.  Because that initial slice is definitionally the zero datum
after the anti-profile cancellation lemma, the BKM-data surface is still exactly
the zero-flow affine-plus-localized pressure classification. -/
theorem BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  rw [BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity
    a f (affineAddScalarSchwartzPressure c π ρ q)]
  constructor
  · intro hData
    rcases
        (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
          c π ρ q hc hπ hρ).1 hData with
      ⟨_hInitial, hcZero, hgradZero⟩
    exact ⟨hcZero, hgradZero⟩
  · rintro ⟨hcZero, hgradZero⟩
    exact
      (BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) (u0 := (0 : NSInitialVelocity))
        c π ρ q hc hπ hρ).2
        ⟨rfl, hcZero, hgradZero⟩

/-- Exact repaired-clause/BKM-data boundary for the full affine-plus-localized
Schwartz pressure class over the cancelled equal-amplitude anti-profile branch.
The repaired finite-energy BKM clause contributes no pressure information at
the zero datum, so the combined clause-and-data package is classified by the
same collapsed affine-plus-localized pressure conditions as BKM data itself. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) a c π ρ f q hc hπ hρ).1 hData
  · intro hPressure
    exact
      ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
        (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) a c π ρ f q hc hπ hρ).2 hPressure⟩

/-- Exact repaired-clause/BKM-data boundary for the syntactic anti-profile
initial datum and the full affine-plus-localized Schwartz pressure class.  The
initial slice cancels to zero, so the paired repaired clause and matching
BKM-data package exists exactly under the same collapsed pressure conditions. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · rintro ⟨_hClause, hData⟩
    exact
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        (ν := ν) (T := T) a c π ρ f q hc hπ hρ).1 hData
  · intro hPressure
    exact
      ⟨by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
            (ExplicitFiniteEnergyBKMContinuationClause_zero ν T),
        (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
          (ν := ν) (T := T) a c π ρ f q hc hπ hρ).2 hPressure⟩

/-- Negative form of the full affine-plus-localized anti-profile BKM
classification.  A nonzero affine spatial coefficient on the certified slab,
or an active localized pressure amplitude paired with a nonzero fixed Schwartz
pressure gradient, rules out BKM data for the cancelled two-mode branch. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  rcases
      (BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        a c π ρ f q hc hπ hρ).1 hData with
    ⟨hcZero, hgradZeroOfActive⟩
  rcases hbad with ⟨t, ht0, htT, hct⟩ | ⟨hactive, s, x, hgrad⟩
  · exact hct (hcZero t ht0 htT)
  · exact hgrad (hgradZeroOfActive hactive s x)

/-- Negative form over the syntactic anti-profile initial datum.  This is the
same obstruction as the zero-datum BKM-data no-go, but phrased on the exact
witness type a repaired finite-mode route would try to cite. -/
theorem not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  intro hData
  rcases
      (BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
        a c π ρ f q hc hπ hρ).1 hData with
    ⟨hcZero, hgradZeroOfActive⟩
  rcases hbad with ⟨t, ht0, htT, hct⟩ | ⟨hactive, s, x, hgrad⟩
  · exact hct (hcZero t ht0 htT)
  · exact hgrad (hgradZeroOfActive hactive s x)

/-- Clause-level separation for the repaired BKM surface.  Even when the bare
finite-energy BKM continuation clause is inhabited at the zero datum, a bad
affine-plus-localized pressure still cannot be packaged as structured BKM data
for the equal-amplitude anti-profile branch. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ⟨ExplicitFiniteEnergyBKMContinuationClause_zero ν T,
      not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
        a c π ρ f q hc hπ hρ hbad⟩

/-- Same data-level separation, phrased over the syntactic anti-profile initial
datum.  The repaired BKM clause may be inhabited for the cancelled finite-mode
initial datum, but the matching structured BKM-data package with a bad
affine-plus-localized pressure is still impossible. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro hData
    exact
      not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
        a c π ρ f q hc hπ hρ hbad hData

/-- Constructor-input separation for the repaired finite-mode BKM clause.  The
generic clause theorem may still inhabit the cancelled initial datum, but the
full pointwise momentum equation needed to use the proposed anti-profile
velocity and bad affine-plus-localized pressure is impossible. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_or_active_schwartzPressureGradient_ne_zero
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hbad :
      (∃ t, c t ≠ 0) ∨
        ((∃ t, ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  constructor
  · simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f] using
      (ExplicitFiniteEnergyBKMContinuationClause_zero ν T)
  · intro heq
    rcases
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
          a ν c π ρ f q).1 heq with
      ⟨hcZero, hgradZeroOfActive⟩
    rcases hbad with ⟨t, hct⟩ | ⟨hactive, s, x, hgrad⟩
    · exact hct (hcZero t)
    · exact hgrad (hgradZeroOfActive hactive s x)

end NavierStokes
end FluidDynamics
end Mettapedia
