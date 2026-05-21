import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstruction

/-!
# Concrete Navier-Stokes Witness Construction Regression

Small theorem-level checks for the direct zero witness and the boxed steady
seed witness classification.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesWitnessConstructionRegression

theorem zero_global_witness_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact zeroNavierStokesGlobalRegularityWitness_nonempty hν

theorem time_independent_seed_classification_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (T : ℝ) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (henergy : finiteInitialKineticEnergy u₀)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (timeIndependentVelocity u₀) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  exact
    timeIndependentVelocity_finiteTimeWitness_iff_stationaryMomentum
      T p hsmooth hdiv henergy hp

theorem time_independent_seed_forward_audit_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x := by
  exact timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum hW

theorem time_independent_seed_exact_classification_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) (p : NSPressureField)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) ↔
      finiteInitialKineticEnergy u₀ ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          spatialConvection (timeIndependentVelocity u₀) t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian (timeIndependentVelocity u₀) t x) := by
  exact
    timeIndependentVelocity_finiteTimeWitness_iff_finiteInitialKineticEnergy_and_stationaryMomentum
      hT p hsmooth hdiv hp

theorem time_independent_seed_forward_audit_zero_time_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p) :
    ∀ x,
      spatialConvection (timeIndependentVelocity u₀) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (timeIndependentVelocity u₀) 0 x := by
  exact
    timeIndependentVelocity_finiteTimeWitness_implies_stationaryMomentum_zero_time
      hT hW

theorem time_independent_seed_pointwise_failure_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (timeIndependentVelocity u₀) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (timeIndependentVelocity u₀) t x) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = timeIndependentVelocity u₀ ∧ W.pressure = p := by
  exact
    not_exists_timeIndependentVelocity_finiteTimeWitness_of_stationaryMomentum_failure
      ht0 htT hfail

theorem zero_velocity_pressure_gradient_audit_regression
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    (hW : ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact zeroVelocity_finiteTimeWitness_implies_spatialPressureGradient_zero hW

theorem zero_velocity_pressure_gradient_classification_regression
    {ν : ℝ} {T : ℝ} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  exact zeroVelocity_finiteTimeWitness_iff_spatialPressureGradient_zero p hp

theorem zero_velocity_time_only_pressure_witness_regression
    {ν : ℝ} {T : ℝ} (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact zeroVelocity_timeOnlyPressure_finiteTimeWitness π hπ

theorem constant_velocity_exact_classification_regression
    {ν : ℝ} {T : ℝ} (hT : 0 ≤ T) {c : NSSpace} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T,
        W.velocity = constantVelocityField c ∧ W.pressure = p) ↔
      c = 0 ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0) := by
  exact
    constantVelocityField_finiteTimeWitness_iff_zero_and_spatialPressureGradient_zero
      hT p hp

theorem constant_initial_velocity_witness_type_inhabited_iff_zero_regression
    {ν : ℝ} {T : ℝ} (hT : 0 ≤ T) {c : NSSpace} :
    Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) ↔
      c = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity_iff hT

theorem zero_velocity_pressure_gradient_failure_regression
    {ν : ℝ} {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail : spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧ W.pressure = p := by
  exact
    not_exists_zeroVelocity_finiteTimeWitness_of_spatialPressureGradient_failure
      ht0 htT hfail

theorem boxed_steady_seed_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_iff_stationaryMomentum
      hν N L u₀ T p hp

theorem boxed_steady_seed_zero_spatial_gradient_pressure_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (p : NSPressureField)
    (hp : smoothSpaceTimePressure p)
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T p hp hp_zero

theorem boxed_steady_seed_time_only_pressure_classification_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t)) ↔
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_iff_stationaryMomentum_zeroPressure
      hν N L u₀ T π hπ

theorem boxed_steady_seed_forward_audit_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ t x, 0 ≤ t → t ≤ T →
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x := by
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum
      hν N L u₀ hW

theorem boxed_steady_seed_forward_audit_zero_time_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    (hT : 0 ≤ T)
    (hW :
      ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p) :
    ∀ x,
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x := by
  exact
    boxedPartialPeriodizationSteadySeed_finiteTimeWitness_implies_stationaryMomentum_zero_time
      hν N L u₀ hT hW

theorem boxed_steady_seed_pointwise_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
          spatialPressureGradient p t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀ ht0 htT hfail

theorem boxed_steady_seed_zero_spatial_gradient_pressure_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} {p : NSPressureField}
    {t : NSTime} {x : NSSpace}
    (hp_zero : ∀ t x, spatialPressureGradient p t x = 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = p := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_zeroSpatialGradientPressure_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀ hp_zero ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_failure_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (π : NSTime → ℝ)
    {T : ℝ} {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
        W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    not_exists_boxedPartialPeriodizationSteadySeed_timeOnlyPressure_finiteTimeWitness_of_stationaryMomentum_failure
      hν N L u₀ π ht0 htT hfail

theorem boxed_steady_seed_time_only_pressure_candidate_gap_regression
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (T : ℝ) (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    {t : NSTime} {x : NSSpace}
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hfail :
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x ≠
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    (smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      boundedKineticEnergyUpTo
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) T) ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity T,
          W.velocity = boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν ∧
            W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) := by
  exact
    boxedPartialPeriodizationSteadySeed_timeOnlyPressure_exhibits_nonMomentumFiniteTimeFields_without_exactWitness
      hν N L u₀ T π hπ ht0 htT hfail

end NavierStokesWitnessConstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
