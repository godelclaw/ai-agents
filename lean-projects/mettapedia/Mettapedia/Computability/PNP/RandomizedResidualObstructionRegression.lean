import Mettapedia.Computability.PNP.RandomizedResidualObstruction

/-!
# Regression checks for randomized residual obstruction

These wrappers pin the product-space reduction: a randomized residual object is
just an ordinary side channel on the finite sample/coin product, so positive
advantage forces joint orbit-resolving mass.
-/

namespace Mettapedia.Computability.PNP.RandomizedResidualObstructionRegression

open Mettapedia.Computability.PNP

section

variable {α Coin U V : Type*} [Fintype α] [Fintype Coin]

theorem randomized_gap_forces_joint_resolved_mass_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      δ ≤ doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    δ ≤ randomizedResidualResolvedMass τ v w coinWeight := by
  exact randomizedResidualResolvedMass_ge_of_le_doubledAdvantage
    τ u v y w coinWeight h δ hτ hu hy hw hδ

theorem coinwise_unresolved_randomized_residual_blocks_positive_advantage_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x c, v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact not_pos_doubledAdvantage_randomizedResidual_of_coinwise_unresolved
    τ u v y w coinWeight h hτ hu hy hw hunresolved

theorem fixed_source_support_randomized_residual_blocks_positive_advantage_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → τ x = x) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact not_pos_doubledAdvantage_randomizedResidual_of_fixed_source_support
    τ u v y w coinWeight h hτ hu hy hw hsupport

theorem supportwise_unresolved_randomized_residual_blocks_positive_advantage_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact not_pos_doubledAdvantage_randomizedResidual_of_supportwise_unresolved
    τ u v y w coinWeight h hτ hu hy hw hunresolved

theorem positive_randomized_advantage_forces_positive_joint_resolution_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    0 < randomizedResidualResolvedMass τ v w coinWeight := by
  exact randomizedResidualResolvedMass_pos_of_pos_doubledAdvantage
    τ u v y w coinWeight h hτ hu hy hw hadv

theorem positive_randomized_advantage_witnesses_resolving_coin_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c := by
  exact exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

theorem positive_randomized_advantage_witnesses_deterministic_coin_slice_regression
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w := by
  exact exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

end

end Mettapedia.Computability.PNP.RandomizedResidualObstructionRegression
