import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeFixedPressureExactClassification
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity

/-!
# Finite-Mode Fixed-Pressure Uniform-Vorticity Classification

This file upgrades the constant-one two-mode fixed-pressure exact
classification to the uniform-vorticity-packaged finite-time surface.

For this concrete velocity family, the uniform-vorticity layer adds no extra
flexibility to the fixed-pressure problem: a uniform-vorticity package exists
exactly when the same velocity/pressure pair is already an exact finite-time
witness, equivalently when the pressure gradient supplies the viscous
Laplacian residual on the certified slab.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Exact uniform-vorticity-data classification for the inviscidly closed
constant-one two-mode branch with a fixed smooth pressure. Once the velocity is
fixed, the only remaining condition is the same slabwise pressure-gradient
compensation identity already forced by exact witness existence. The explicit
uniform vorticity bound for the constant-one two-mode velocity supplies the
packaging in the reverse direction. -/
theorem oneOneTwoModeSchwartzVelocity_uniformVorticityData_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
    {ν T : ℝ} (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hp : smoothSpaceTimePressure p)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = p ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  constructor
  · rintro ⟨W, hWvel, hWpress, _B, _hω⟩
    exact
      (oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
        (ν := ν) (T := T) p f g hp hfDiv hgDiv hclosure).1 ⟨W, hWvel, hWpress⟩
  · intro hpressure
    rcases
        (oneOneTwoModeSchwartzVelocity_finiteTimeWitness_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
          (ν := ν) (T := T) p f g hp hfDiv hgDiv hclosure).2 hpressure with
      ⟨W, hWvel, hWpress⟩
    refine
      ⟨W, hWvel, hWpress,
        schwartzInitialVelocityVorticityBound f +
          schwartzInitialVelocityVorticityBound g, ?_⟩
    simpa [hWvel] using
      (uniformVorticityBoundUpTo_twoModeSchwartzVelocity_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp)
        (by intro t; simp))

/-- Manuscript-facing uniform-vorticity classification specialized to the
affine-plus-localized Schwartz pressure family. -/
theorem
    oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_uniformVorticityData_iff_inviscidClosure_pressureGradient_lapSum_on
    {ν T : ℝ} (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  exact
    oneOneTwoModeSchwartzVelocity_uniformVorticityData_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T)
      (p := affineAddScalarSchwartzPressure c π ρ q)
      f g
      (smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q)
      hfDiv hgDiv hclosure

/-- For positive viscosity, the zero-pressure constant-one two-mode
uniform-vorticity branch survives exactly when the summed viscous Laplacian
residual already vanishes throughout the certified slab. This is the
constructive converse to the previous fixed-pressure zero-pressure uniform
obstruction. -/
theorem oneOneTwoModeSchwartzVelocity_zeroPressure_uniformVorticityData_iff_inviscidClosure_lapSum_zero_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ↔
      ∀ t x, 0 ≤ t → t ≤ T →
        spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        (0 : NSSpace) := by
  have hpZero : smoothSpaceTimePressure (0 : NSPressureField) := by
    have hAffine :
        smoothSpaceTimePressure
          (affineAddScalarSchwartzPressure
            (fun _ : NSTime => 0)
            (fun _ : NSTime => 0)
            (fun _ : NSTime => 0)
            (0 : 𝓢(NSSpace, ℝ))) := by
      exact smoothSpaceTimePressure_affineAddScalarSchwartzPressure
        (c := fun _ : NSTime => 0)
        (π := fun _ : NSTime => 0)
        (ρ := fun _ : NSTime => 0)
        (q := (0 : 𝓢(NSSpace, ℝ)))
        contDiff_const contDiff_const contDiff_const
    have hZero :
        affineAddScalarSchwartzPressure
            (fun _ : NSTime => 0)
            (fun _ : NSTime => 0)
            (fun _ : NSTime => 0)
            (0 : 𝓢(NSSpace, ℝ)) =
          (0 : NSPressureField) := by
      funext t x
      simp [affineAddScalarSchwartzPressure]
    simpa [hZero] using hAffine
  have hiff :=
    oneOneTwoModeSchwartzVelocity_uniformVorticityData_pressure_iff_inviscidClosure_pressureGradient_lapSum_on
      (ν := ν) (T := T) (p := (0 : NSPressureField)) f g hpZero hfDiv hgDiv hclosure
  constructor
  · intro hData
    have hgrad := hiff.1 hData
    intro t x ht0 htT
    have hsmul :
        (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) =
          0 := by
      simpa [spatialPressureGradient_zero] using (hgrad t x ht0 htT).symm
    exact (smul_eq_zero.mp hsmul).resolve_left hν.ne'
  · intro hlap
    apply hiff.2
    intro t x ht0 htT
    calc
      spatialPressureGradient (0 : NSPressureField) t x = 0 := spatialPressureGradient_zero t x
      _ =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
            simp [hlap t x ht0 htT]

end NavierStokes
end FluidDynamics
end Mettapedia
