import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeAntiProfileGlobalOutputObstruction

/-! Regression tests for exact global-output anti-profile obstructions. -/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem equalAmplitudeAntiProfile_timeOnlyPressure_exactGlobalOutput_regression
    (ν : ℝ) (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
      ν
      (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
      (twoModeSchwartzVelocity a a f (-f))
      (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero
      (ν := ν)
      a
      f
      (p := fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)).2
      (fun t x => spatialPressureGradient_timeOnly π t x)

theorem equalAmplitudeAntiProfile_coord0AffinePressure_noExactGlobalOutput_regression
    {ν c : ℝ} (hc : c ≠ 0) (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        (fun _ : NSTime => fun x : NSSpace => ⟪EuclideanSpace.single nsCoord0 c, x⟫) := by
  apply
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) a f
  refine ⟨0, 0, ?_⟩
  intro hzero
  have hgrad :
      spatialPressureGradient
          (fun _ : NSTime => fun x : NSSpace => ⟪EuclideanSpace.single nsCoord0 c, x⟫) 0 0 =
        EuclideanSpace.single nsCoord0 c := by
    simpa using
      spatialPressureGradient_affinePressure
        (fun _ : NSTime => EuclideanSpace.single nsCoord0 c)
        (fun _ : NSTime => 0)
        0
        0
  have hcoordzero : c = 0 := by
    have hcoord :=
      congrArg (fun v : NSSpace => v nsCoord0) (hgrad.symm.trans hzero)
    simpa [nsCoord0] using hcoord
  exact hc hcoordzero

theorem
    equalAmplitudeAntiProfile_affineAddScalarSchwartzPressure_exactGlobalOutputCollapse_regression
    (ν : ℝ) (a π ρ : NSTime → ℝ) (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f))
        (twoModeSchwartzVelocity a a f (-f))
        (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π ρ q)) ↔
      ((∃ t, ρ t ≠ 0) →
        ∀ s x,
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  simpa using
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_equalAmplitudeAntiProfileInitialVelocity_velocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
      (ν := ν)
      a
      (fun _ : NSTime => 0)
      π
      ρ
      f
      q
      contDiff_const
      hπ
      hρ)

end NavierStokes
end FluidDynamics
end Mettapedia
