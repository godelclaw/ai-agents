import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity

/-!
# Navier-Stokes Schwartz directional-rigidity regression

Focused theorem-level checks for the Schwartz directional-rigidity obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesSchwartzDirectionalRigidityRegression

/-- Concrete basis direction used in the regression checks. -/
def e1 : NSSpace := EuclideanSpace.single ⟨1, by decide⟩ (1 : ℝ)

theorem e1_ne_zero : e1 ≠ 0 := by
  intro h
  have := congrArg (fun x : NSSpace => x ⟨1, by decide⟩) h
  simp [e1] at this

theorem zero_initialVelocity_translationInvariantAlong_regression :
    TranslationInvariantAlong e1 ((0 : NSSchwartzInitialVelocity) : NSInitialVelocity) := by
  intro x s
  simp [e1]

theorem translationInvariantAlong_basis_direction_forces_zero_regression
    (u₀ : NSSchwartzInitialVelocity)
    (hinv : TranslationInvariantAlong e1 (u₀ : NSInitialVelocity)) :
    (u₀ : NSInitialVelocity) = 0 := by
  exact schwartzInitialVelocity_eq_zero_of_translationInvariantAlong u₀ e1_ne_zero hinv

theorem vanishing_basis_direction_fderiv_forces_zero_regression
    (u₀ : NSSchwartzInitialVelocity)
    (hzero : ∀ x : NSSpace, fderiv ℝ (fun z : NSSpace => u₀ z) x e1 = 0) :
    (u₀ : NSInitialVelocity) = 0 := by
  exact schwartzInitialVelocity_eq_zero_of_fderiv_eq_zero_along u₀ e1_ne_zero hzero

theorem zero_initialVelocity_basis_direction_fderiv_regression :
    ∀ x : NSSpace, fderiv ℝ (fun z : NSSpace => (0 : NSSchwartzInitialVelocity) z) x e1 = 0 := by
  intro x
  simp [e1]

theorem zero_initialVelocity_vanishing_basis_direction_fderiv_regression :
    ((0 : NSSchwartzInitialVelocity) : NSInitialVelocity) = 0 := by
  exact
    vanishing_basis_direction_fderiv_forces_zero_regression
      (0 : NSSchwartzInitialVelocity)
      zero_initialVelocity_basis_direction_fderiv_regression

end NavierStokesSchwartzDirectionalRigidityRegression
end NavierStokes
end FluidDynamics
end Mettapedia
