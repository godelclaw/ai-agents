import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLinearShearObstruction

/-!
# Navier-Stokes Schwartz linear-shear obstruction regression

Focused theorem-level checks for the affine linear-shear Schwartz obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzLinearShearObstructionRegression

theorem translationInvariantAlong_unit_linearShearFullDrift_streamwise_regression :
    TranslationInvariantAlong linearShearStreamwiseDirection
      (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise 1 1 1

theorem linearShearFullDriftInitialVelocity_eq_zero_iff_regression
    (a b c : ℝ) :
    linearShearFullDriftInitialVelocity a b c = (0 : NSInitialVelocity) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact linearShearFullDriftInitialVelocity_eq_zero_iff

theorem not_exists_schwartzInitialVelocity_eq_unit_linearShearInitialVelocity_regression :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearInitialVelocity 1 := by
  exact
    not_exists_schwartzInitialVelocity_eq_linearShearInitialVelocity_of_shear_ne_zero
      (a := 1) (by norm_num)

theorem not_exists_schwartzInitialVelocity_eq_unit_linearShearFullDriftInitialVelocity_regression :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity 1 1 1 := by
  exact
    not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := 1) (b := 1) (c := 1) (Or.inl (by norm_num))

end NavierStokesSchwartzLinearShearObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
