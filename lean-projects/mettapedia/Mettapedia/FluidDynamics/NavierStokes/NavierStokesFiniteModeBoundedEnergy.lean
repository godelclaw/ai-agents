import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyContinuationBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzData
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Navier-Stokes Finite-Mode Bounded-Energy Constructions

This file records the first positive finite-mode replacement for the
whole-space linear-growth obstruction: finite-dimensional velocity ansatzes
built from Schwartz spatial profiles and uniformly bounded scalar amplitudes.
These modes are finite-energy objects before any closure claim for the
Navier-Stokes equation is imposed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Two spatial Schwartz profiles with scalar time amplitudes, viewed as a
finite-mode velocity field on `ℝ × ℝ^3`. -/
def twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) :
    NSVelocityField :=
  fun t x => a t • f x + b t • g x

/-- The initial velocity slice associated to two Schwartz profiles and fixed
scalar amplitudes. -/
def twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    NSInitialVelocity :=
  fun x => a0 • f x + b0 • g x

/-- The pressure class used by the existing two-mode energy bridge: an affine
gauge plus one localized Schwartz pressure profile. -/
def affineAddScalarSchwartzPressure
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) :
    NSPressureField :=
  (fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) +
    fun t : NSTime => fun x : NSSpace => ρ t * q x

/-- Smooth time amplitudes multiplying Schwartz spatial profiles give a smooth
two-mode concrete space-time velocity field. -/
theorem smoothSpaceTimeVelocity_twoModeSchwartzVelocity
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) := by
  have haTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => a tx.1) :=
    ha.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hbTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => b tx.1) :=
    hb.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hfSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => (f : NSSpace → NSSpace) tx.2) :=
    f.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  have hgSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => (g : NSSpace → NSSpace) tx.2) :=
    g.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, twoModeSchwartzVelocity] using
    (haTime.smul hfSpace).add (hbTime.smul hgSpace)

/-- Smooth affine pressure coefficients and a smooth scalar amplitude on a
Schwartz pressure profile give a smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_affineAddScalarSchwartzPressure
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) := by
  simpa [affineAddScalarSchwartzPressure] using
    smoothSpaceTimePressure_affine_add_scalar_smul_schwartzPressure hc hπ hρ q

/-- Smooth scalar amplitudes have the expected derivative witnesses with
`deriv`; this removes separate derivative bookkeeping from finite-mode
constructors. -/
theorem hasDerivAt_deriv_of_contDiff {a : NSTime → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    ∀ t, HasDerivAt a (deriv a t) t := by
  intro t
  exact ((ha.differentiable (by simp)) t).hasDerivAt

/-- Two-mode Schwartz initial data have finite kinetic energy on `ℝ^3`. -/
theorem finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    finiteInitialKineticEnergy (twoModeSchwartzInitialVelocity a0 b0 f g) := by
  simpa [twoModeSchwartzInitialVelocity] using
    finiteInitialKineticEnergy_of_schwartzInitialVelocity
      ((a0 • f + b0 • g : NSSchwartzInitialVelocity))

/-- Two-mode Schwartz initial data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    smoothInitialVelocityData (twoModeSchwartzInitialVelocity a0 b0 f g) := by
  simpa [twoModeSchwartzInitialVelocity] using
    smoothInitialVelocityData_of_schwartzInitialVelocity
      ((a0 • f + b0 • g : NSSchwartzInitialVelocity))

/-- The divergence of a two-mode Schwartz initial slice is the corresponding
scalar combination of the profile divergences. -/
theorem initialSpatialDivergence_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) (x : NSSpace) :
    initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x =
      a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
        b0 * initialSpatialDivergence (g : NSInitialVelocity) x := by
  calc
    initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x =
        initialSpatialDivergence
          (a0 • (f : NSInitialVelocity) + b0 • (g : NSInitialVelocity)) x := by
          rfl
    _ =
        initialSpatialDivergence (a0 • (f : NSInitialVelocity)) x +
          initialSpatialDivergence (b0 • (g : NSInitialVelocity)) x := by
          rw [initialSpatialDivergence_add
            (f.differentiableAt.const_smul a0)
            (g.differentiableAt.const_smul b0)]
    _ =
        a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
          initialSpatialDivergence (b0 • (g : NSInitialVelocity)) x := by
          rw [initialSpatialDivergence_const_smul]
    _ =
        a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
          b0 * initialSpatialDivergence (g : NSInitialVelocity) x := by
          rw [initialSpatialDivergence_const_smul]

/-- Two-mode Schwartz initial data built from divergence-free profiles are
divergence-free themselves. -/
theorem initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    ∀ x, initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x = 0 := by
  intro x
  rw [initialSpatialDivergence_twoModeSchwartzInitialVelocity a0 b0 f g x, hfDiv x, hgDiv x]
  simp

/-- The two-mode space-time field matches its declared initial slice. -/
theorem MatchesInitialVelocity_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) :
    MatchesInitialVelocity
      (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (twoModeSchwartzVelocity a b f g) := by
  intro x
  rfl

/-- The time derivative of a smooth two-mode Schwartz velocity is the
two-mode velocity built from the scalar derivatives. -/
theorem timeVelocityDerivative_twoModeSchwartzVelocity_deriv
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x =
        deriv a t • f x + deriv b t • g x := by
  intro t x
  simpa [twoModeSchwartzVelocity] using
    timeVelocityDerivative_add_scalar_smul
      a (deriv a) b (deriv b) (f : NSSpace → NSSpace) (g : NSSpace → NSSpace)
      (hasDerivAt_deriv_of_contDiff ha)
      (hasDerivAt_deriv_of_contDiff hb) t x

/-- The spatial Laplacian of a two-mode Schwartz velocity expands modewise. -/
theorem spatialLaplacian_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (twoModeSchwartzVelocity a b f g) t x =
      a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  have hf2 :
      ContDiffAt ℝ 2
        (fun y : NSSpace => (timeIndependentVelocity (f : NSInitialVelocity)) t y) x := by
    exact (f.smooth'.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  have hg2 :
      ContDiffAt ℝ 2
        (fun y : NSSpace => (timeIndependentVelocity (g : NSInitialVelocity)) t y) x := by
    exact (g.smooth'.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  change
    spatialLaplacian
        ((a t) • timeIndependentVelocity (f : NSInitialVelocity) +
          (b t) • timeIndependentVelocity (g : NSInitialVelocity)) t x =
      a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x
  rw [spatialLaplacian_add (hf2.const_smul (a t)) (hg2.const_smul (b t))]
  rw [spatialLaplacian_const_smul (a t) hf2,
    spatialLaplacian_const_smul (b t) hg2]

/-- The nonlinear convection term of a two-mode Schwartz velocity expands into
the two self-interactions and the two mixed directional-derivative terms. -/
theorem spatialConvection_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialConvection (twoModeSchwartzVelocity a b f g) t x =
      (a t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
        (b t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  have hf :
      DifferentiableAt ℝ
        (fun y : NSSpace => (timeIndependentVelocity (f : NSInitialVelocity)) t y) x := by
    simpa [timeIndependentVelocity] using f.differentiableAt
  have hg :
      DifferentiableAt ℝ
        (fun y : NSSpace => (timeIndependentVelocity (g : NSInitialVelocity)) t y) x := by
    simpa [timeIndependentVelocity] using g.differentiableAt
  simpa [twoModeSchwartzVelocity, timeIndependentVelocity] using
    spatialConvection_linearCombination (a t) (b t) hf hg

/-- Expanded residual closure implies the pointwise Navier-Stokes momentum
equation for arbitrary two-mode Schwartz amplitudes.  This is the nonzero-mode
version of the momentum slot: the nonlinear term is exposed as the full
self/mixed convection expansion rather than hidden inside the old `heq`
hypothesis. -/
theorem momentumEquation_twoModeSchwartzVelocity_of_explicitClosure
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
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
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv ha hb f g t x,
    spatialConvection_twoModeSchwartzVelocity a b f g t x,
    spatialLaplacian_twoModeSchwartzVelocity a b f g t x]
  exact hclosure t x

/-- Expanded residual closure implies the pointwise Navier-Stokes momentum
equation for arbitrary two-mode Schwartz amplitudes and arbitrary
time-indexed Schwartz pressure slices.  This is the pressure-slice analogue of
`momentumEquation_twoModeSchwartzVelocity_of_explicitClosure`; it exposes the
same derivative, convection, and Laplacian terms while replacing the
affine-plus-localized pressure ansatz by the actual pressure-slice field. -/
theorem momentumEquation_twoModeSchwartzVelocity_schwartzPressureSlice_of_explicitClosure
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : NSTime → 𝓢(NSSpace, ℝ))
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
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv ha hb f g t x,
    spatialConvection_twoModeSchwartzVelocity a b f g t x,
    spatialLaplacian_twoModeSchwartzVelocity a b f g t x]
  exact hclosure t x

/-- Constant nonzero amplitudes `a(t)=b(t)=1` are a direct specialization of
the expanded two-mode momentum theorem.  The closure hypothesis is the explicit
nonlinear self/mixed convection balance for the two spatial Schwartz profiles. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_of_explicitClosure
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    momentumEquation_twoModeSchwartzVelocity_of_explicitClosure
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const ν c π ρ f g q ?_
  intro t x
  simpa using hclosure t x

/-- In the inviscid zero-pressure specialization, constant nonzero amplitudes
`a(t)=b(t)=1` satisfy the pointwise momentum equation as soon as the explicit
two-profile convection expansion vanishes.  This isolates the exact remaining
profile-level closure burden for nonzero finite-energy Schwartz modes. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_inviscid_zeroPressure_of_convectionClosure
    (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (0 : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialPressureGradient_zero]
  simpa using hclosure t x

/-- Conversely, a constant-one two-mode Schwartz velocity with zero pressure
can satisfy the pointwise momentum equation only if the expanded convection
residual equals the viscous Laplacian residual.  This exposes the precise
extra condition that is absent from the inviscid zero-pressure branch. -/
theorem explicitClosure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_momentumEquation
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (hmom : ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  intro t x
  have h := hmom t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialPressureGradient_zero] at h
  simpa using h

/-- The inviscid zero-pressure one-one branch cannot be reused as a
positive-viscosity zero-pressure Navier--Stokes branch unless the summed
profile Laplacian vanishes everywhere.  A single nonzero Laplacian-sum point
contradicts the momentum equation. -/
theorem not_momentumEquation_oneOneTwoMode_zeroPressure_of_inviscidClosure_lapSum_ne_zero
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hlap : ∃ t x,
        spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x ≠
        (0 : NSSpace)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hlap with ⟨t, x, hlap_ne⟩
  have hresidual :=
    explicitClosure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_momentumEquation
      ν f g hmom t x
  have hsmul :
      (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) =
        0 := by
    rw [← hresidual, hclosure t x]
  exact hlap_ne ((smul_eq_zero.mp hsmul).resolve_left hν.ne')

/-- Once the constant-one two-mode branch has inviscid convection closure,
the full positive-viscosity momentum equation is exactly the assertion that
the pressure gradient supplies the missing viscous Laplacian residual.  This
is the minimal pressure-repair condition left after the zero-pressure
obstruction. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
    (ν : ℝ) (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x) ↔
      ∀ t x,
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  constructor
  · intro hmom t x
    have h := hmom t x
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at h
    simpa [hclosure t x] using h
  · intro hpressure t x
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
    simpa [hclosure t x] using hpressure t x

/-- Pointwise mismatch with the viscous Laplacian residual blocks every
pressure-repaired positive-viscosity realization of the same inviscid
constant-one two-mode branch. -/
theorem not_momentumEquation_oneOneTwoMode_of_inviscidClosure_pressureGradient_lapSum_mismatch
    (ν : ℝ) (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x,
        spatialPressureGradient p t x ≠
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hbad with ⟨t, x, hbad⟩
  exact hbad
    ((momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
      ν p f g hclosure).1 hmom t x)

/-- A constant-one two-mode Schwartz velocity is genuinely nonzero whenever the
two spatial profiles do not cancel everywhere. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero
    (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0) :
    ∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace) := by
  rcases hfg with ⟨x, hx⟩
  refine ⟨0, x, ?_⟩
  simpa [twoModeSchwartzVelocity] using hx

/-- The zero-amplitude member of the two-mode Schwartz class is literally the
zero velocity field, independently of the chosen spatial Schwartz profiles. -/
theorem twoModeSchwartzVelocity_zero_zero
    (f g : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g =
      (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- If the affine coefficient and localized Schwartz pressure amplitude both
vanish, the affine-plus-Schwartz pressure class reduces to a time-only pressure
gauge. -/
theorem affineAddScalarSchwartzPressure_zero_timeOnly
    (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) :
    affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
        (fun _ : NSTime => 0) q =
      fun t : NSTime => fun _ : NSSpace => π t := by
  funext t x
  simp [affineAddScalarSchwartzPressure]

/-- The spatial gradient of an affine-in-space pressure gauge
`p(t,x)=⟪c(t),x⟫+π(t)` is exactly the affine coefficient `c(t)`. -/
theorem spatialPressureGradient_affinePressure
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x =
      c t := by
  unfold spatialPressureGradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    ((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)

/-- In the affine-plus-Schwartz pressure class, if the localized Schwartz
amplitude is zero, the spatial pressure gradient is exactly the spatial affine
coefficient.  The time-only scalar gauge and unused Schwartz profile do not
contribute. -/
theorem spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
      c t := by
  have hpress :
      affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q =
        fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s := by
    funext s y
    simp [affineAddScalarSchwartzPressure]
  rw [hpress]
  exact spatialPressureGradient_affinePressure c π t x

/-- Any finite-time witness with zero velocity and pure spatial-affine pressure
has zero affine pressure coefficient throughout its certified time slab.  Thus a
nonzero spatial affine pressure gradient cannot be hidden as pressure gauge on a
zero-flow finite-time witness. -/
theorem ExplicitFiniteTimeRegularityWitness.zeroVelocity_spatialAffinePressure_implies_zeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u0 T)
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hWvel : W.velocity = (0 : NSVelocityField))
    (hWpress :
      W.pressure = affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) :
    ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  intro t ht0 htT
  have hmom := W.momentum_equation_on t (0 : NSSpace) ht0 htT
  have hlap : spatialLaplacian (0 : NSVelocityField) t (0 : NSSpace) = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t (0 : NSSpace)
  simpa [hWvel, hWpress, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap,
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c π q t
      (0 : NSSpace)] using hmom

/-- The zero-amplitude two-mode Schwartz velocity satisfies the pointwise
Navier-Stokes momentum equation against any time-only pressure gauge represented
inside the affine-plus-Schwartz pressure class.  This closes the momentum
identity for a finite-energy Schwartz member of the construction without an
external `heq` hypothesis. -/
theorem momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x := by
  intro t x
  simpa [twoModeSchwartzVelocity_zero_zero f g,
    affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x

/-- Unit smooth bump at the origin of physical space.  This supplies a concrete
nonzero compactly supported smooth profile, hence a Schwartz profile. -/
def nsUnitBumpScalar : ContDiffBump (0 : NSSpace) := default

/-- A compactly supported smooth first-coordinate bump. -/
def nsUnitBumpVectorFun : NSSpace → NSSpace :=
  fun x => nsUnitBumpScalar x • EuclideanSpace.single nsCoord0 (1 : ℝ)

/-- A concrete nonzero Schwartz velocity profile, obtained from a compactly
supported bump. -/
def nsUnitBumpSchwartzVelocity : NSSchwartzInitialVelocity :=
  ((nsUnitBumpScalar.hasCompactSupport.smul_right :
      HasCompactSupport nsUnitBumpVectorFun).toSchwartzMap <| by
    simpa [nsUnitBumpVectorFun] using
      (nsUnitBumpScalar.contDiff.smul
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : NSSpace => EuclideanSpace.single nsCoord0 (1 : ℝ))))

/-- The concrete bump profile is nonzero at the origin. -/
theorem nsUnitBumpSchwartzVelocity_nonzero_at_origin :
    nsUnitBumpSchwartzVelocity (0 : NSSpace) ≠ 0 := by
  have hbump : nsUnitBumpScalar (0 : NSSpace) = 1 := by
    exact nsUnitBumpScalar.one_of_mem_closedBall
      (Metric.mem_closedBall_self nsUnitBumpScalar.rIn_pos.le)
  have hvalue : nsUnitBumpSchwartzVelocity (0 : NSSpace) =
      EuclideanSpace.single nsCoord0 (1 : ℝ) := by
    simp [nsUnitBumpSchwartzVelocity, hbump]
  intro hzero
  have hcoord : (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 = 1 := by
    simp [nsCoord0]
  have : (0 : NSSpace) nsCoord0 = 1 := by
    rw [← hcoord, ← hvalue, hzero]
  norm_num at this

/-- The concrete bump profile is nonzero. -/
theorem nsUnitBumpSchwartzVelocity_nonzero :
    ∃ x : NSSpace, nsUnitBumpSchwartzVelocity x ≠ 0 :=
  ⟨0, nsUnitBumpSchwartzVelocity_nonzero_at_origin⟩

/-- Equal constant amplitudes applied to a profile and its negative cancel as
a two-mode space-time velocity field. -/
theorem oneOneAntiProfileSchwartzVelocity_zero
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) =
      (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- Equal constant amplitudes applied to a profile and its negative cancel on
the initial slice. -/
theorem oneOneAntiProfileSchwartzInitialVelocity_zero
    (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzInitialVelocity 1 1 f (-f) =
      (0 : NSInitialVelocity) := by
  funext x
  simp [twoModeSchwartzInitialVelocity]

/-- Equal time-dependent amplitudes applied to a profile and its negative
cancel as a two-mode space-time velocity field. -/
theorem equalAmplitudeAntiProfileSchwartzVelocity_zero
    (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- Equal scalar amplitudes applied to a profile and its negative cancel on
the initial slice. -/
theorem equalAmplitudeAntiProfileSchwartzInitialVelocity_zero
    (a0 : ℝ) (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzInitialVelocity a0 a0 f (-f) =
      (0 : NSInitialVelocity) := by
  funext x
  simp [twoModeSchwartzInitialVelocity]

/-- For a nonzero profile, an anti-profile two-mode velocity is identically
zero exactly when the two scalar amplitudes are pointwise equal.  This makes
the cancellation boundary exact: unequal amplitudes cannot hide inside the
`f, -f` ansatz as another zero-flow repair. -/
theorem antiProfileSchwartzVelocity_eq_zero_iff_equalAmplitude
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0) :
    twoModeSchwartzVelocity a b f (-f) = (0 : NSVelocityField) ↔
      ∀ t, a t = b t := by
  constructor
  · intro hzero t
    rcases hf with ⟨x, hx⟩
    have hpoint : a t • f x + b t • (-(f x)) = 0 := by
      have htx := congrFun (congrFun hzero t) x
      simpa [twoModeSchwartzVelocity] using htx
    have hscale : (a t - b t) • f x = 0 := by
      calc
        (a t - b t) • f x = a t • f x - b t • f x := by
          rw [sub_smul]
        _ = a t • f x + -(b t • f x) := by
          rw [sub_eq_add_neg]
        _ = a t • f x + b t • (-(f x)) := by
          simp
        _ = 0 := hpoint
    have hsub : a t - b t = 0 := by
      rcases smul_eq_zero.mp hscale with hcoeff | hprofile
      · exact hcoeff
      · exact False.elim (hx hprofile)
    exact sub_eq_zero.mp hsub
  · intro heq
    funext t x
    simp [twoModeSchwartzVelocity, heq t]

/-- For a nonzero profile, an anti-profile initial slice is zero exactly when
the two initial scalar amplitudes are equal. -/
theorem antiProfileSchwartzInitialVelocity_eq_zero_iff_equalAmplitude
    (a0 b0 : ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0) :
    twoModeSchwartzInitialVelocity a0 b0 f (-f) = (0 : NSInitialVelocity) ↔
      a0 = b0 := by
  constructor
  · intro hzero
    rcases hf with ⟨x, hx⟩
    have hpoint : a0 • f x + b0 • (-(f x)) = 0 := by
      have hxzero := congrFun hzero x
      simpa [twoModeSchwartzInitialVelocity] using hxzero
    have hscale : (a0 - b0) • f x = 0 := by
      calc
        (a0 - b0) • f x = a0 • f x - b0 • f x := by
          rw [sub_smul]
        _ = a0 • f x + -(b0 • f x) := by
          rw [sub_eq_add_neg]
        _ = a0 • f x + b0 • (-(f x)) := by
          simp
        _ = 0 := hpoint
    have hsub : a0 - b0 = 0 := by
      rcases smul_eq_zero.mp hscale with hcoeff | hprofile
      · exact hcoeff
      · exact False.elim (hx hprofile)
    exact sub_eq_zero.mp hsub
  · intro heq
    funext x
    simp [twoModeSchwartzInitialVelocity, heq]

/-- If the scalar amplitudes differ somewhere and the profile is nonzero, the
anti-profile two-mode velocity is nonzero somewhere. -/
theorem exists_antiProfileSchwartzVelocity_ne_zero_of_exists_amplitude_ne
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0)
    (hab : ∃ t, a t ≠ b t) :
    ∃ t x, twoModeSchwartzVelocity a b f (-f) t x ≠ 0 := by
  by_contra hnone
  have hzero : twoModeSchwartzVelocity a b f (-f) = (0 : NSVelocityField) := by
    funext t x
    by_contra htx
    exact hnone ⟨t, x, htx⟩
  have heq := (antiProfileSchwartzVelocity_eq_zero_iff_equalAmplitude a b f hf).mp hzero
  rcases hab with ⟨t, ht⟩
  exact ht (heq t)

/-- A profile paired with its negative satisfies the full positive-viscosity
momentum equation against any time-only pressure gauge in the affine-plus-
Schwartz pressure class.  The cancellation is recorded explicitly, so this is a
residual-closure baseline rather than a non-cancelling finite-mode flow. -/
theorem momentumEquation_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
    {ν : ℝ} (_hν : 0 < ν) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x := by
  intro t x
  simpa [oneOneAntiProfileSchwartzVelocity_zero f,
    affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x

/-- Equal time-dependent amplitudes applied to a profile and its negative
satisfy the momentum equation against any time-only affine-plus-Schwartz
pressure gauge.  The pressure may be nonzero as a function of time, but the
velocity field is still the zero flow. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineTimeOnlyPressure
    (a : NSTime → ℝ) (ν : ℝ) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  intro t x
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  simpa [hvel, affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x

/-- A zero equal-amplitude anti-profile cannot satisfy the momentum equation
against a pure spatial-affine pressure unless that affine coefficient is
identically zero.  This rules out repairing the cancellation branch by inserting
a nonzero spatial affine pressure gradient. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_implies_zeroAffineCoeff
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hME :
      ∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient
              (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) :
    ∀ t, c t = 0 := by
  intro t
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t (0 : NSSpace) = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t (0 : NSSpace)
  simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap,
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c π q t
      (0 : NSSpace)] using hME t (0 : NSSpace)

/-- Contrapositive form of the spatial-affine pressure obstruction: if the
affine pressure coefficient is nonzero at some time, the equal-amplitude
anti-profile zero flow cannot satisfy the Navier-Stokes momentum equation with
that pure spatial-affine pressure. -/
theorem not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeff
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ∃ t, c t ≠ 0) :
    ¬
      (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient
              (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) := by
  intro hME
  rcases hc with ⟨t, ht⟩
  exact ht
    (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_spatialAffinePressure_implies_zeroAffineCoeff
      a ν c π f q hME t)

/-- Expanded residual closure for the anti-profile construction, with positive
viscosity and a time-only affine-plus-Schwartz pressure. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) (π : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :=
    momentumEquation_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
      hν π f q t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x] at hmom
  simpa using hmom

/-- Equal time-dependent amplitudes applied to a profile and its negative
satisfy the momentum equation against the zero time-indexed Schwartz pressure
slice for every viscosity.  The result is still a zero-flow cancellation
baseline, but it removes the artificial unit-amplitude restriction. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  intro t x
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  simpa [hvel] using momentumEquation_zeroVelocityField_zeroPressure ν t x

/-- Expanded pressure-slice residual closure for the equal-amplitude
anti-profile construction.  This is a generalized cancellation baseline: the
time derivative, convection, and Laplacian expansions all cancel because the
actual velocity field is identically zero. -/
theorem explicitClosure_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a)
    (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
      deriv a t • f x + deriv a t • (-f) x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * a t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
              (a t * a t) •
                spatialFDeriv
                  (timeIndependentVelocity
                    (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
                  t x (f x) +
              (a t ^ (2 : ℕ)) •
                spatialConvection
                  (timeIndependentVelocity
                    (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
                  t x) +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            a t • spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :=
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
      a ν f t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := a) (b := a) ha ha f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity a a f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity a a f (-f) t x] at hmom
  simpa using hmom

/-- Expanded residual closure for the anti-profile construction with zero
pressure. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_zeroPressure_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hclosure :=
    explicitClosure_oneOneAntiProfileSchwartzVelocity_affineTimeOnlyPressure_of_posViscosity
      hν (fun _ : NSTime => 0) f (0 : 𝓢(NSSpace, ℝ)) t x
  have hp :
      affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
          (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
        (0 : NSPressureField) := by
    funext s y
    simp [affineAddScalarSchwartzPressure]
  simpa [hp] using hclosure

/-- Expanded residual closure for the anti-profile construction with the zero
time-indexed Schwartz pressure slice.  This is the pressure-slice version of
the cancellation baseline above. -/
theorem explicitClosure_oneOneAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
    (ν : ℝ) (f : NSSchwartzInitialVelocity) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x ((-f) x) +
            spatialFDeriv
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x (f x) +
            spatialConvection
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)))
              t x) := by
  intro t x
  have hmom :
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f)) t x := by
    simpa [oneOneAntiProfileSchwartzVelocity_zero f] using
      momentumEquation_zeroVelocityField_zeroPressure ν t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f (-f) t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f (-f) t x] at hmom
  simpa using hmom

/-- There are nonzero Schwartz profiles and an explicit pressure field
(`p = 0`) satisfying the expanded full-viscous residual closure for every
positive viscosity.  The two profile contributions cancel in the resulting
two-mode velocity, so this theorem is a concrete closure sanity check for the
residual expansion. -/
theorem exists_nonzeroSchwartzProfiles_pressure_explicitClosure_fullViscousNS_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) :
    ∃ f g : NSSchwartzInitialVelocity, ∃ p : NSPressureField,
      (∃ x : NSSpace, f x ≠ 0) ∧
      (∃ x : NSSpace, g x ≠ 0) ∧
      (∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) := by
  refine ⟨nsUnitBumpSchwartzVelocity, -nsUnitBumpSchwartzVelocity, 0, ?_, ?_, ?_⟩
  · exact nsUnitBumpSchwartzVelocity_nonzero
  · rcases nsUnitBumpSchwartzVelocity_nonzero with ⟨x, hx⟩
    exact ⟨x, by simpa using neg_ne_zero.mpr hx⟩
  · simpa using
      explicitClosure_oneOneAntiProfileSchwartzVelocity_zeroPressure_of_posViscosity
        hν nsUnitBumpSchwartzVelocity

/-- The divergence of a two-mode Schwartz velocity is the scalar-amplitude
combination of the initial divergences of its spatial profiles. -/
theorem spatialDivergence_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialDivergence (twoModeSchwartzVelocity a b f g) t x =
      a t * initialSpatialDivergence (f : NSInitialVelocity) x +
        b t * initialSpatialDivergence (g : NSInitialVelocity) x := by
  have hf :
      spatialDivergence (fun s : NSTime => fun y : NSSpace => a s • f y) t x =
        a t * initialSpatialDivergence (f : NSInitialVelocity) x := by
    simpa [spatialDivergence, spatialFDeriv, timeIndependentVelocity,
      initialSpatialDivergence] using
      spatialDivergence_const_smul
        (a t) (timeIndependentVelocity (f : NSInitialVelocity)) t x
  have hg :
      spatialDivergence (fun s : NSTime => fun y : NSSpace => b s • g y) t x =
        b t * initialSpatialDivergence (g : NSInitialVelocity) x := by
    simpa [spatialDivergence, spatialFDeriv, timeIndependentVelocity,
      initialSpatialDivergence] using
      spatialDivergence_const_smul
        (b t) (timeIndependentVelocity (g : NSInitialVelocity)) t x
  change
    spatialDivergence
      ((fun s : NSTime => fun y : NSSpace => a s • f y) +
        fun s : NSTime => fun y : NSSpace => b s • g y) t x =
      a t * initialSpatialDivergence (f : NSInitialVelocity) x +
        b t * initialSpatialDivergence (g : NSInitialVelocity) x
  rw [spatialDivergence_add]
  · rw [hf, hg]
  · exact f.differentiableAt.const_smul (a t)
  · exact g.differentiableAt.const_smul (b t)

/-- Two-mode Schwartz velocities built from divergence-free spatial profiles
are incompressible for all times. -/
theorem spatialDivergence_twoModeSchwartzVelocity_zero
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    ∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0 := by
  intro t x
  rw [spatialDivergence_twoModeSchwartzVelocity a b f g t x, hfDiv x, hgDiv x]
  simp

/-- Uniformly bounded scalar amplitudes give global bounded kinetic energy for
the two-mode Schwartz finite-mode velocity. -/
theorem boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergy (twoModeSchwartzVelocity a b f g) := by
  simpa [twoModeSchwartzVelocity] using
    boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
      a b f g A B haBound hbBound

/-- The same two-mode Schwartz finite-mode velocity has bounded kinetic energy
on every finite time slab. -/
theorem boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T :=
  boundedKineticEnergy_implies_boundedKineticEnergyUpTo
    (boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
      a b f g A B haBound hbBound)

/-- A compact positive package for bounded-energy finite-mode exploration:
the initial slice is finite-energy, the space-time field matches it, and the
velocity has slab-bounded kinetic energy. -/
theorem twoModeSchwartzVelocity_finiteInitial_matches_boundedEnergyUpTo_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- The same positive finite-mode package, now also discharging space-time
smoothness from smooth scalar amplitudes. -/
theorem twoModeSchwartzVelocity_finiteInitial_smooth_matches_boundedEnergyUpTo_of_abs_le
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- The positive finite-mode package with both smoothness and
incompressibility discharged from profile-level divergence freeness. -/
theorem twoModeSchwartzVelocity_finiteInitial_smooth_matches_divergenceFree_boundedEnergyUpTo_of_abs_le
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      (∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- A bounded two-mode Schwartz ansatz satisfying the full pointwise
Navier--Stokes equation gives a genuine global explicit output on `ℝ^3`. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
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
    ExplicitConcreteNavierStokesGlobalOutput
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) := by
  refine ⟨twoModeSchwartzVelocity a b f g, affineAddScalarSchwartzPressure c π ρ q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q
  · exact heq
  · exact spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
        a b f g A B haBound hbBound

/-- The same bounded two-mode Schwartz ansatz therefore satisfies the repaired
explicit finite-energy whole-space clause. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
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
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

/-- On a positive-viscosity datum, the same bounded two-mode Schwartz ansatz
also inhabits the repaired structured fully concrete clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 < ν)
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
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := twoModeSchwartzInitialVelocity (a 0) (b 0) f g
         smooth_initial :=
           smoothInitialVelocityData_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
         divergence_free_initial :=
           initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
             (a 0) (b 0) f g hfDiv hgDiv
         finite_initial_energy :=
           finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν
      (smoothInitialVelocityData_twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
        (a 0) (b 0) f g hfDiv hgDiv)
      (finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

/-- Finite-time witness constructor for the two-mode Schwartz finite-mode
velocity and affine-plus-Schwartz pressure class.  The bounded-energy field is
supplied by the proved two-profile energy bridge; the momentum, smoothness and
incompressibility hypotheses remain explicit. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu : smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g))
    (hp : smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q))
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    (by simpa [twoModeSchwartzVelocity] using hu)
    (by simpa [affineAddScalarSchwartzPressure] using hp)
    (by simpa [twoModeSchwartzVelocity] using hinit)
    hν haBound hbBound ha hb
    (by
      intro t x
      simpa [twoModeSchwartzVelocity, affineAddScalarSchwartzPressure] using heq t x)
    (by
      intro t x
      simpa [twoModeSchwartzVelocity] using hdiv t x)

/-- Finite-time witness constructor for the same two-mode Schwartz class that
derives velocity and pressure smoothness from smooth coefficient curves.  The
remaining analytic obligations are the pointwise momentum equation,
incompressibility, coefficient bounds and initial matching. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    (smoothSpaceTimeVelocity_twoModeSchwartzVelocity haSmooth hbSmooth f g)
    (smoothSpaceTimePressure_affineAddScalarSchwartzPressure
      hcSmooth hπSmooth hρSmooth q)
    hinit hν haBound hbBound ha hb heq hdiv

/-- Finite-time witness constructor for the two-mode Schwartz class that
derives both smoothness and incompressibility from smooth coefficient curves
and divergence-free Schwartz spatial profiles. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν haBound hbBound ha hb heq
    (spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv)

/-- Canonical-initial finite-time witness constructor for the smooth
divergence-free two-mode Schwartz class.  The scalar derivative witnesses and
initial matching proof are derived internally from smoothness and the
definition of the initial slice. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteTimeRegularityWitness ν
      (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
    (ν := ν) (T := T)
    (u₀ := twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
    a (deriv a) b (deriv b) f g A B c π ρ q
    haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv
    (MatchesInitialVelocity_twoModeSchwartzVelocity a b f g)
    hν haBound hbBound
    (hasDerivAt_deriv_of_contDiff haSmooth)
    (hasDerivAt_deriv_of_contDiff hbSmooth)
    heq

/-- A finite-time regularity witness for the inviscid zero-pressure
constant-amplitude two-mode Schwartz construction.  All smoothness, initial
matching, bounded-energy and incompressibility obligations are discharged by
the finite-mode infrastructure; the only remaining analytic input is the
explicit two-profile convection closure. -/
def ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ExplicitFiniteTimeRegularityWitness 0
      (twoModeSchwartzInitialVelocity 1 1 f g) T := by
  refine
    ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      (f := f) (g := g) (A := 1) (B := 1)
      (c := fun _ : NSTime => 0) (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0) (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0) (T := T)
      contDiff_const contDiff_const contDiff_const contDiff_const contDiff_const
      hfDiv hgDiv (by norm_num) ?_ ?_ ?_
  · intro t
    simp
  · intro t
    simp
  · intro t x
    have hp :
        affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
          (0 : NSPressureField) := by
      funext s y
      simp [affineAddScalarSchwartzPressure]
    simpa [hp] using
      momentumEquation_oneOneTwoModeSchwartzVelocity_inviscid_zeroPressure_of_convectionClosure
        f g hclosure t x

/-- The inviscid zero-pressure constant-amplitude package is genuinely
nonzero whenever the two spatial Schwartz profiles do not cancel everywhere. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_inviscidWitness_of_convectionClosure
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
      Nonempty
        (ExplicitFiniteTimeRegularityWitness 0
          (twoModeSchwartzInitialVelocity 1 1 f g) T) := by
  exact
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg,
      ⟨ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
        f g hfDiv hgDiv hclosure⟩⟩

end NavierStokes
end FluidDynamics
end Mettapedia
