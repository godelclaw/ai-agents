import Mettapedia.Computability.PNP.ResolutionDemandObstruction

/-!
# Regression checks for residual side-channel resolution demands

These wrappers pin the strengthened residual-side-information obstruction:
positive advantage from an invariant feature plus a residual side channel forces
positive orbit-resolving side-channel mass.
-/

namespace Mettapedia.Computability.PNP.ResolutionDemandObstructionRegression

open Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

theorem claimed_gap_forces_matching_resolved_mass_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      δ ≤ doubledAdvantage (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w := by
  exact resolvedMass_ge_of_le_doubledAdvantage_pair
    τ u v y w h δ hτ hu hy hw hδ

theorem half_accuracy_gap_forces_matching_resolved_mass_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      weightedTotalMass w + δ ≤
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w := by
  exact
    resolvedMass_ge_of_total_plus_delta_le_two_mul_weightedCorrectMass_pair
      τ u v y w h δ hτ hu hy hw hδ

theorem zero_resolved_mass_blocks_positive_advantage_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hres : resolvedMass τ v w = 0) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
    τ u v y w h hτ hu hy hw hres

theorem positive_advantage_forces_positive_resolved_mass_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  exact resolvedMass_pos_of_pos_doubledAdvantage_pair
    τ u v y w h hτ hu hy hw hadv

theorem strict_half_accuracy_advantage_forces_positive_resolved_mass_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  exact
    resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      τ u v y w h hτ hu hy hw hadv

theorem unresolved_side_channel_has_zero_resolved_mass_regression
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hunresolved : ∀ x, v (τ x) = v x) :
    resolvedMass τ v w = 0 := by
  exact resolvedMass_eq_zero_of_unresolved τ v w hunresolved

theorem supportwise_unresolved_side_channel_blocks_positive_advantage_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact
    not_pos_doubledAdvantage_pair_of_supportwise_unresolved
      τ u v y w h hτ hu hy hw hunresolved

theorem positive_resolved_mass_exposes_resolving_point_regression
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hmass : 0 < resolvedMass τ v w) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact exists_resolving_point_of_pos_resolvedMass τ v w hmass

theorem positive_advantage_exposes_resolving_point_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    exists_resolving_point_of_pos_doubledAdvantage_pair
      τ u v y w h hτ hu hy hw hadv

theorem strict_half_accuracy_advantage_exposes_resolving_point_regression
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
      τ u v y w h hτ hu hy hw hadv

end

end Mettapedia.Computability.PNP.ResolutionDemandObstructionRegression
