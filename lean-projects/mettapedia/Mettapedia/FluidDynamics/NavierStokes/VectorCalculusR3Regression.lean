import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3

/-!
# Vector Calculus `R^3` Regression

Small theorem-level checks for the bottom-up concrete `ℝ × ℝ^3` calculus lane.

Positive examples:
- zero and constant fields satisfy the exact zero-pressure momentum identity;
- steady affine shear and damped/transported heat-shear identities replay on
  concrete parameters.

Negative examples:
- unit linear shear has genuinely nonzero vorticity;
- transported heat shear with nonzero transport speed has genuinely nonzero
  convection at the spacetime origin.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace VectorCalculusR3Regression

theorem zero_velocity_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  simpa using momentumEquation_zeroVelocityField_zeroPressure ν t x

theorem constant_velocity_momentum_regression
    (ν : ℝ) (c : NSSpace) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x +
        spatialConvection (constantVelocityField c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (constantVelocityField c) t x := by
  simpa using momentumEquation_constantVelocityField_zeroPressure ν c t x

theorem zero_velocity_time_only_pressure_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => s ^ (2 : ℕ) + 1) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  simpa using
    momentumEquation_zeroVelocityField_timeOnlyPressure
      ν (fun s : NSTime => s ^ (2 : ℕ) + 1) t x

theorem constant_velocity_time_only_pressure_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField (EuclideanSpace.single nsCoord2 1)) t x +
        spatialConvection (constantVelocityField (EuclideanSpace.single nsCoord2 1)) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => s) t x =
      ν • spatialLaplacian (constantVelocityField (EuclideanSpace.single nsCoord2 1)) t x := by
  simpa using
    momentumEquation_constantVelocityField_timeOnlyPressure
      ν (EuclideanSpace.single nsCoord2 1) (fun s : NSTime => s) t x

theorem linear_shear_horizontal_drift_momentum_regression
    (ν a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField a b) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField a b) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      ν • spatialLaplacian (linearShearHorizontalDriftVelocityField a b) t x := by
  simpa using momentumEquation_linearShearHorizontalDriftVelocityField ν a b t x

theorem linear_shear_horizontal_drift_time_only_pressure_momentum_regression
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialPressureGradient
          (linearShearHorizontalDriftPressureField 1 1 +
            fun s : NSTime => fun _ : NSSpace => s ^ (2 : ℕ)) t x =
      ν • spatialLaplacian (linearShearHorizontalDriftVelocityField 1 1) t x := by
  have hp :
      DifferentiableAt ℝ (fun y : NSSpace => linearShearHorizontalDriftPressureField 1 1 t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice
      (smoothSpaceTimePressure_linearShearHorizontalDriftPressureField 1 1) t x
  exact momentumEquation_addTimeOnlyPressure
    (u := linearShearHorizontalDriftVelocityField 1 1)
    (p := linearShearHorizontalDriftPressureField 1 1)
    (π := fun s : NSTime => s ^ (2 : ℕ))
    hp
    (momentumEquation_linearShearHorizontalDriftVelocityField ν 1 1 t x)

theorem heat_shear_full_drift_momentum_regression
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialConvection (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearFullDriftVelocityField ν a k d c) t x := by
  simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure ν a k d c t x

theorem heat_shear_transport_full_drift_momentum_regression
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x := by
  simpa using momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure
    ν a k b d c t x

theorem heat_shear_transport_full_drift_time_only_pressure_momentum_regression
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => s + 1) t x =
      ν • spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x := by
  have hp : DifferentiableAt ℝ (fun y : NSSpace => (0 : NSPressureField) t y) x := by
    simp
  simpa [zero_add] using
    momentumEquation_addTimeOnlyPressure
      (u := heatShearTransportFullDriftVelocityField ν a k b d c)
      (p := (0 : NSPressureField))
      (π := fun s : NSTime => s + 1)
      hp
      (momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure ν a k b d c t x)

theorem linear_shear_unit_vorticity_nonzero_regression :
    spatialVorticity (linearShearVelocityField 1) 0 0 ≠ 0 := by
  rw [spatialVorticity_linearShearVelocityField]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  simp [nsCoord2] at hcoord

theorem transported_heat_shear_unit_convection_nonzero_regression :
    spatialConvection (heatShearTransportVelocityField 0 1 1 1) 0 0 ≠ 0 := by
  rw [spatialConvection_heatShearTransportVelocityField]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord0) h
  simp [coord0Embedding_apply, nsCoord0, nsCoord1] at hcoord

end VectorCalculusR3Regression
end NavierStokes
end FluidDynamics
end Mettapedia
