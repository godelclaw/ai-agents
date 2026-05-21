import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSpatialAffinePressureGaugeRigidity

/-!
# Spatial-Affine Pressure Gauge Rigidity Regression

Focused regression checks for the spatial-affine specialization of exact-surface
pressure-gauge rigidity.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSpatialAffinePressureGaugeRigidityRegression

theorem same_velocity_spatialAffinePressure_witness_retarget_regression
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
  exact
    exists_finiteTimeWitness_with_sameVelocity_spatialAffinePressure_iff_affineCoeff_eq_on
      (ν := ν) (u₀ := u₀) (T := T) (u := u)
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ hW

theorem same_velocity_spatialAffinePressure_global_output_retarget_regression
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
  exact
    ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_spatialAffinePressure_iff_affineCoeff_eq
      (ν := ν) (u₀ := u₀) (u := u)
      c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂ h

theorem oneOne_twoMode_spatialAffinePressure_repair_collapse_regression
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
  exact
    oneOneTwoModeSchwartzVelocity_spatialAffinePressure_repair_iff_affineCoeff_eq_on
      (ν := ν) (T := T) f g c₁ c₂ π₁ π₂ q₁ q₂ hc₁ hc₂ hπ₁ hπ₂
      hfDiv hgDiv hclosure hrepair₁

end NavierStokesSpatialAffinePressureGaugeRigidityRegression
end NavierStokes
end FluidDynamics
end Mettapedia
