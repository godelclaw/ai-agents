import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactClassification
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesPressureGaugeRigidity

/-!
# Spatial-Affine Pressure Gauge Rigidity

This file specializes the general exact-surface pressure-gauge rigidity theorem
to the manuscript's affine-plus-localized pressure family in the zero
localized-amplitude subcase.

For pressures of the form `affineAddScalarSchwartzPressure c π 0 q`, the exact
finite-time and exact global-output surfaces for a fixed velocity depend only on
the spatial affine coefficient `c`.  The time-only scalar term `π` and the idle
Schwartz profile `q` are pure gauge.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The spatial gradient of the difference of two zero-localized
affine-plus-Schwartz pressures is exactly the difference of their spatial
affine coefficients.  Thus the time-only scalar gauges and idle Schwartz
profiles completely disappear from the exact-surface pressure comparison. -/
theorem spatialPressureGradient_sub_affineAddScalarSchwartzPressure_spatialAffine
    (c₁ c₂ : NSTime → NSSpace) (π₁ π₂ : NSTime → ℝ) (q₁ q₂ : 𝓢(NSSpace, ℝ))
    (hc₁ : ContDiff ℝ ∞ c₁) (hc₂ : ContDiff ℝ ∞ c₂)
    (hπ₁ : ContDiff ℝ ∞ π₁) (hπ₂ : ContDiff ℝ ∞ π₂)
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂ -
          affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁) t x =
      c₂ t - c₁ t := by
  have hp₁ :
      smoothSpaceTimePressure
        (affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc₁ hπ₁ contDiff_const q₁
  have hp₂ :
      smoothSpaceTimePressure
        (affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂) :=
    smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc₂ hπ₂ contDiff_const q₂
  rw [spatialPressureGradient_sub
      (smoothSpaceTimePressure_differentiableAt_spatialSlice hp₂ t x)
      (smoothSpaceTimePressure_differentiableAt_spatialSlice hp₁ t x),
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c₂ π₂ q₂ t x,
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c₁ π₁ q₁ t x]

/-- On the exact finite-time witness surface for a fixed velocity, replacing one
zero-localized affine-plus-Schwartz pressure by another is possible exactly
when the spatial affine coefficients agree on the certified slab.  The time-only
scalar terms and idle Schwartz profiles are pure pressure gauge. -/
theorem exists_finiteTimeWitness_with_sameVelocity_spatialAffinePressure_iff_affineCoeff_eq_on
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {u : NSVelocityField}
    (c₁ c₂ : NSTime → NSSpace) (π₁ π₂ : NSTime → ℝ) (q₁ q₂ : 𝓢(NSSpace, ℝ))
    (hc₁ : ContDiff ℝ ∞ c₁) (hc₂ : ContDiff ℝ ∞ c₂)
    (hπ₁ : ContDiff ℝ ∞ π₁) (hπ₂ : ContDiff ℝ ∞ π₂)
    (hW :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u ∧
          W.pressure = affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁) :
    (∃ W' : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W'.velocity = u ∧
          W'.pressure = affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂) ↔
      ∀ t, 0 ≤ t → t ≤ T → c₂ t = c₁ t := by
  let p₁ : NSPressureField := affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁
  let p₂ : NSPressureField := affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂
  have hp₂ : smoothSpaceTimePressure p₂ := by
    simpa [p₂] using
      smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc₂ hπ₂ contDiff_const q₂
  have hiff :=
    exists_finiteTimeWitness_with_sameVelocity_pressure_iff_pressureDifference_zeroGradient_on
      (u := u) (p := p₁) (q := p₂) hW hp₂
  constructor
  · intro hW₂ t ht0 htT
    have hzero := (hiff.mp hW₂) t (0 : NSSpace) ht0 htT
    rw [show p₂ - p₁ =
        affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂ -
          affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁ by rfl] at hzero
    rw [spatialPressureGradient_sub_affineAddScalarSchwartzPressure_spatialAffine
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ t (0 : NSSpace)] at hzero
    exact sub_eq_zero.mp hzero
  · intro hcoeff
    apply hiff.mpr
    intro t x ht0 htT
    rw [show p₂ - p₁ =
        affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂ -
          affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁ by rfl]
    rw [spatialPressureGradient_sub_affineAddScalarSchwartzPressure_spatialAffine
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ t x]
    exact sub_eq_zero.mpr (hcoeff t ht0 htT)

/-- On the exact whole-space output surface for a fixed velocity, zero-localized
affine-plus-Schwartz pressures are rigid modulo their spatial affine
coefficient.  The time-only scalar gauges and idle Schwartz profiles do not
create genuinely different exact global outputs. -/
theorem
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_spatialAffinePressure_iff_affineCoeff_eq
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (c₁ c₂ : NSTime → NSSpace) (π₁ π₂ : NSTime → ℝ) (q₁ q₂ : 𝓢(NSSpace, ℝ))
    (hc₁ : ContDiff ℝ ∞ c₁) (hc₂ : ContDiff ℝ ∞ c₂)
    (hπ₁ : ContDiff ℝ ∞ π₁) (hπ₂ : ContDiff ℝ ∞ π₂)
    (h :
      ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u
        (affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁)) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure ν u₀ u
        (affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂) ↔
      ∀ t, c₂ t = c₁ t := by
  let p₁ : NSPressureField := affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁
  let p₂ : NSPressureField := affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂
  have hp₂ : smoothSpaceTimePressure p₂ := by
    simpa [p₂] using
      smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc₂ hπ₂ contDiff_const q₂
  have hiff :=
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_iff_pressureDifference_zeroGradient
      (p := p₁) (q := p₂) h hp₂
  constructor
  · intro h₂ t
    have hzero := (hiff.mp h₂) t (0 : NSSpace)
    rw [show p₂ - p₁ =
        affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂ -
          affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁ by rfl] at hzero
    rw [spatialPressureGradient_sub_affineAddScalarSchwartzPressure_spatialAffine
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ t (0 : NSSpace)] at hzero
    exact sub_eq_zero.mp hzero
  · intro hcoeff
    apply hiff.mpr
    intro t x
    rw [show p₂ - p₁ =
        affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂ -
          affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁ by rfl]
    rw [spatialPressureGradient_sub_affineAddScalarSchwartzPressure_spatialAffine
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ t x]
    exact sub_eq_zero.mpr (hcoeff t)

/-- Concrete one-one two-mode specialization: once one spatial-affine repair
coefficient closes the constant-one branch, every other zero-localized
affine-plus-Schwartz pressure repairs the same exact finite-time surface if and
only if it has the same spatial affine coefficient on the certified slab. -/
theorem oneOneTwoModeSchwartzVelocity_spatialAffinePressure_repair_iff_affineCoeff_eq_on
    {ν T : ℝ} (f g : NSSchwartzInitialVelocity)
    (c₁ c₂ : NSTime → NSSpace) (π₁ π₂ : NSTime → ℝ) (q₁ q₂ : 𝓢(NSSpace, ℝ))
    (hc₁ : ContDiff ℝ ∞ c₁) (hc₂ : ContDiff ℝ ∞ c₂)
    (hπ₁ : ContDiff ℝ ∞ π₁) (hπ₂ : ContDiff ℝ ∞ π₂)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hrepair₁ : ∀ t x, 0 ≤ t → t ≤ T →
        c₁ t =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c₂ π₂ (fun _ : NSTime => 0) q₂) ↔
      ∀ t, 0 ≤ t → t ≤ T → c₂ t = c₁ t := by
  let p₁ : NSPressureField := affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁
  have hp₁ : smoothSpaceTimePressure p₁ := by
    simpa [p₁] using
      smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc₁ hπ₁ contDiff_const q₁
  have hW₁ :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = p₁ := by
    refine
      (oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
        (ν := ν) (T := T) p₁ f g hp₁ hfDiv hgDiv hclosure).2 ?_
    intro t x ht0 htT
    rw [show p₁ = affineAddScalarSchwartzPressure c₁ π₁ (fun _ : NSTime => 0) q₁ by rfl]
    rw [spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c₁ π₁ q₁ t x]
    exact hrepair₁ t x ht0 htT
  simpa [p₁] using
    exists_finiteTimeWitness_with_sameVelocity_spatialAffinePressure_iff_affineCoeff_eq_on
      (ν := ν) (u₀ := twoModeSchwartzInitialVelocity 1 1 f g) (T := T)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ hW₁

end NavierStokes
end FluidDynamics
end Mettapedia
