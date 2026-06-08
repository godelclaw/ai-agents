import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundation

/-!
# P vs NP grassroots: finite-coin postprocessing improvement obstruction

The postprocessing foundation already proves that observed-support-injective
postprocessing preserves finite-coin tolerance and output defect exactly.
This file packages the contrapositive route consequence: if deterministic
postprocessing strictly improves either surface, then it must merge distinct
observed original outputs.
-/

namespace Mettapedia.Computability.PNP

/-- If no two distinct observed original outputs collide under a deterministic
postprocessor, then that postprocessor is injective on the observed support. -/
theorem observedInjective_of_no_observedOutput_collision
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (hnone :
      ¬ ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
        r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2)) :
    ∀ b1 c1 b2 c2,
      g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
  intro b1 c1 b2 c2 hEq
  by_contra hne
  exact hnone ⟨b1, c1, b2, c2, hne, hEq⟩

/-- If postprocessing makes a finite-coin tolerance-`τ` certificate true while
the original recoding still fails it, then two distinct observed original
outputs must collide.  Strict approximate improvement is impossible under
support-injective relabeling. -/
theorem exists_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  by_contra hnone
  apply hnot
  exact
    (countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      r g τ
      (observedInjective_of_no_observedOutput_collision r g hnone)).mp hpost

/-- The same strict-tolerance improvement produces a genuinely nontrivial
postprocessed preimage fiber. -/
theorem exists_postprocessedFiber_card_gt_one_of_postcompose_tolerance_of_not_tolerance
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ z : β, 1 < (finiteOutputPreimageFiber g z).card := by
  classical
  rcases exists_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
      r g τ hpost hnot with ⟨b1, c1, b2, c2, hne, hEq⟩
  refine ⟨g (r b1 c1), ?_⟩
  rw [Finset.one_lt_card]
  refine ⟨r b1 c1, ?_, r b2 c2, ?_, hne⟩
  · simp [finiteOutputPreimageFiber]
  · simp [finiteOutputPreimageFiber, hEq]

/-- If deterministic postprocessing strictly lowers the finite-coin output
defect, then two distinct observed original outputs must collide.  Exact
supportwise relabeling cannot improve the quantitative defect budget. -/
theorem exists_observedOutput_collision_of_postcompose_outputDefect_lt
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  by_contra hnone
  have heq :=
    countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
      r g (observedInjective_of_no_observedOutput_collision r g hnone)
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The defect-improvement form likewise forces some postprocessed output fiber
to merge at least two distinct original outputs. -/
theorem exists_postprocessedFiber_card_gt_one_of_postcompose_outputDefect_lt
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ z : β, 1 < (finiteOutputPreimageFiber g z).card := by
  classical
  rcases exists_observedOutput_collision_of_postcompose_outputDefect_lt r g hlt
    with ⟨b1, c1, b2, c2, hne, hEq⟩
  refine ⟨g (r b1 c1), ?_⟩
  rw [Finset.one_lt_card]
  refine ⟨r b1 c1, ?_, r b2 c2, ?_, hne⟩
  · simp [finiteOutputPreimageFiber]
  · simp [finiteOutputPreimageFiber, hEq]

end Mettapedia.Computability.PNP
