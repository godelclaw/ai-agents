import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch08InfiniteGraphs

set_option linter.unusedSectionVars false

open SimpleGraph

namespace AutoBooks.GraphTheory.Diestel.Ch08Regression

inductive TwoStepStarVertex
  | center
  | middle (n : ℕ)
  | leaf (n : ℕ)
  deriving DecidableEq, Nonempty

open TwoStepStarVertex

def TwoStepStarAdj : TwoStepStarVertex → TwoStepStarVertex → Prop
  | center, middle _ => True
  | middle _, center => True
  | middle n, leaf m => n = m
  | leaf n, middle m => n = m
  | _, _ => False

def twoStepStar : SimpleGraph TwoStepStarVertex where
  Adj := TwoStepStarAdj
  symm := by
    rintro (_ | n | n) (_ | m | m) <;> simp [TwoStepStarAdj, eq_comm]
  loopless := by
    refine ⟨?_⟩
    intro x
    cases x <;> simp [TwoStepStarAdj]

instance : DecidableRel twoStepStar.Adj := by
  intro x y
  cases x <;> cases y <;> simp [twoStepStar, TwoStepStarAdj]
  all_goals infer_instance

def leafSet : Set TwoStepStarVertex :=
  Set.range leaf

private theorem reachable_center (v : TwoStepStarVertex) :
    twoStepStar.Reachable v center := by
  cases v with
  | center =>
      exact .rfl
  | middle n =>
      exact (by simp [twoStepStar, TwoStepStarAdj] : twoStepStar.Adj (middle n) center).reachable
  | leaf n =>
      exact ((by
        simp [twoStepStar, TwoStepStarAdj] : twoStepStar.Adj (leaf n) (middle n)).reachable).trans
        ((by
          simp [twoStepStar, TwoStepStarAdj] : twoStepStar.Adj (middle n) center).reachable)

theorem twoStepStar_connected : twoStepStar.Connected where
  preconnected u v :=
    (reachable_center u).trans (reachable_center v).symm

theorem leafSet_infinite : leafSet.Infinite := by
  simpa [leafSet] using Set.infinite_range_of_injective (fun _ _ h => leaf.inj h)

private theorem noncenter_two_step_eq {a b c : TwoStepStarVertex}
    (ha : a ≠ center) (hb : b ≠ center) (hc : c ≠ center)
    (hab : twoStepStar.Adj a b) (hbc : twoStepStar.Adj b c) :
    a = c := by
  cases a <;> cases b <;> cases c <;>
    simp [twoStepStar, TwoStepStarAdj] at ha hb hc hab hbc ⊢
  · exact hab.trans hbc
  · exact hab.trans hbc

private theorem no_three_noncenter_at (f : ℕ → TwoStepStarVertex)
    (hAdj₀ : twoStepStar.Adj (f 0) (f 1))
    (hAdj₁ : twoStepStar.Adj (f 1) (f 2))
    (h0 : f 0 ≠ center) (h1 : f 1 ≠ center) (h2 : f 2 ≠ center) :
    f 0 = f 2 :=
  noncenter_two_step_eq h0 h1 h2 hAdj₀ hAdj₁

private theorem no_three_noncenter_tail (f : ℕ → TwoStepStarVertex)
    (hAdj₃ : twoStepStar.Adj (f 3) (f 4))
    (hAdj₄ : twoStepStar.Adj (f 4) (f 5))
    (h3 : f 3 ≠ center) (h4 : f 4 ≠ center) (h5 : f 5 ≠ center) :
    f 3 = f 5 :=
  noncenter_two_step_eq h3 h4 h5 hAdj₃ hAdj₄

private theorem twoStepStar_not_isRay (f : ℕ → TwoStepStarVertex) :
    ¬AutoBooks.GraphTheory.Diestel.Ch08.IsRay twoStepStar f := by
  intro hRay
  rcases hRay with ⟨hinj, hadj⟩
  have hblock012 :
      (f 0 ≠ center) → (f 1 ≠ center) → (f 2 ≠ center) → False := by
    intro h0 h1 h2
    have h02 := no_three_noncenter_at f (hadj 0) (hadj 1) h0 h1 h2
    have : (0 : ℕ) = 2 := hinj h02
    omega
  have hblock345 :
      (f 3 ≠ center) → (f 4 ≠ center) → (f 5 ≠ center) → False := by
    intro h3 h4 h5
    have h35 := no_three_noncenter_tail f (hadj 3) (hadj 4) h3 h4 h5
    have : (3 : ℕ) = 5 := hinj h35
    omega
  by_cases h012 : f 0 = center ∨ f 1 = center ∨ f 2 = center
  · have h3 : f 3 ≠ center := by
      intro h3
      rcases h012 with h0 | h12
      · have : (0 : ℕ) = 3 := hinj (by rw [h0, h3])
        omega
      · rcases h12 with h1 | h2
        · have : (1 : ℕ) = 3 := hinj (by rw [h1, h3])
          omega
        · have : (2 : ℕ) = 3 := hinj (by rw [h2, h3])
          omega
    have h4 : f 4 ≠ center := by
      intro h4
      rcases h012 with h0 | h12
      · have : (0 : ℕ) = 4 := hinj (by rw [h0, h4])
        omega
      · rcases h12 with h1 | h2
        · have : (1 : ℕ) = 4 := hinj (by rw [h1, h4])
          omega
        · have : (2 : ℕ) = 4 := hinj (by rw [h2, h4])
          omega
    have h5 : f 5 ≠ center := by
      intro h5
      rcases h012 with h0 | h12
      · have : (0 : ℕ) = 5 := hinj (by rw [h0, h5])
        omega
      · rcases h12 with h1 | h2
        · have : (1 : ℕ) = 5 := hinj (by rw [h1, h5])
          omega
        · have : (2 : ℕ) = 5 := hinj (by rw [h2, h5])
          omega
    exact hblock345 h3 h4 h5
  · have h0 : f 0 ≠ center := fun h0 => h012 (Or.inl h0)
    have h1 : f 1 ≠ center := fun h1 => h012 (Or.inr (Or.inl h1))
    have h2 : f 2 ≠ center := fun h2 => h012 (Or.inr (Or.inr h2))
    exact hblock012 h0 h1 h2

theorem twoStepStar_not_hasComb :
    ¬AutoBooks.GraphTheory.Diestel.Ch08.HasComb twoStepStar leafSet := by
  intro hComb
  obtain ⟨f, hRay, _⟩ := hComb
  exact twoStepStar_not_isRay f hRay

theorem twoStepStar_not_hasStar :
    ¬AutoBooks.GraphTheory.Diestel.Ch08.HasStar twoStepStar leafSet := by
  intro hStar
  rcases hStar with ⟨c, hc⟩
  cases c with
  | center =>
      have : {u | u ∈ leafSet ∧ twoStepStar.Adj center u} = (∅ : Set TwoStepStarVertex) := by
        ext u
        cases u <;> simp [leafSet, twoStepStar, TwoStepStarAdj]
      simp [this] at hc
  | middle n =>
      have : {u | u ∈ leafSet ∧ twoStepStar.Adj (middle n) u} = {leaf n} := by
        ext u
        cases u <;> simp [leafSet, twoStepStar, TwoStepStarAdj, eq_comm]
      simp [this] at hc
  | leaf n =>
      have : {u | u ∈ leafSet ∧ twoStepStar.Adj (leaf n) u} = (∅ : Set TwoStepStarVertex) := by
        ext u
        cases u <;> simp [leafSet, twoStepStar, TwoStepStarAdj]
      simp [this] at hc

theorem current_star_comb_encodings_counterexample :
    twoStepStar.Connected ∧ leafSet.Infinite ∧
      ¬(AutoBooks.GraphTheory.Diestel.Ch08.HasComb twoStepStar leafSet ∨
        AutoBooks.GraphTheory.Diestel.Ch08.HasStar twoStepStar leafSet) := by
  refine ⟨twoStepStar_connected, leafSet_infinite, ?_⟩
  intro h
  rcases h with hComb | hStar
  · exact twoStepStar_not_hasComb hComb
  · exact twoStepStar_not_hasStar hStar

end AutoBooks.GraphTheory.Diestel.Ch08Regression
