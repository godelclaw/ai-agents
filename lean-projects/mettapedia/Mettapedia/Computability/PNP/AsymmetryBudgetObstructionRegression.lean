import Mettapedia.Computability.PNP.AsymmetryBudgetObstruction

/-!
# Regression checks for asymmetry-budget obstruction

These wrappers pin the support-level form of the asymmetry budget: strict
advantage over half accuracy must expose positive-weight mass outside the
unresolved symmetric slice.
-/

namespace Mettapedia.Computability.PNP.AsymmetryBudgetObstructionRegression

open Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

theorem support_inside_symmetric_slice_blocks_strict_advantage_regression
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_support_subset
      τ p u y w h hτ hp hu hy hw hsupport

theorem strict_advantage_forces_positive_outside_mass_regression
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    0 < outsideMass p w := by
  exact
    pos_outsideMass_of_total_lt_two_mul_weightedCorrectMass
      τ p u y w h hτ hp hu hy hw hadv

theorem strict_advantage_exposes_outside_support_regression
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x := by
  exact
    exists_support_outside_of_total_lt_two_mul_weightedCorrectMass
      τ p u y w h hτ hp hu hy hw hadv

end

end Mettapedia.Computability.PNP.AsymmetryBudgetObstructionRegression
