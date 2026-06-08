import Mettapedia.Computability.PNP.InvariantScoreObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: invariant-score signal comes only from weight asymmetry

If the retained score inputs are involution-invariant and the target flips under
the involution, then any signed correlation carried by an invariant soft score
must come entirely from the antisymmetric part of the weighting.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

/-- The contribution of one sample point to an invariant signed-score sum. -/
def signedScoreContribution
    (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ) (x : α) : ℤ :=
  (w x : ℤ) * score (u x) * targetSign (y x)

/-- The antisymmetric part of the weight contribution along one involution pair. -/
def antisymmetricWeightContribution
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ) (x : α) : ℤ :=
  ((w x : ℤ) - (w (τ x) : ℤ)) * score (u x) * targetSign (y x)

/-- For invariant score inputs and target-flipping involution, twice the total
signed score equals the total contribution of the antisymmetric weight part. -/
theorem two_mul_signedScore_sum_eq_antisymmetricWeight_sum
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    2 * ∑ x : α, signedScoreContribution u y w score x
      = ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
  let f : α → ℤ := signedScoreContribution u y w score
  have hbij : Function.Bijective τ := by
    refine ⟨hτ.injective, ?_⟩
    intro x
    exact ⟨τ x, hτ x⟩
  have hsum :
      ∑ x : α, f x = ∑ x : α, f (τ x) := by
    refine Fintype.sum_equiv (Equiv.ofBijective τ hbij) f (fun x : α => f (τ x)) ?_
    intro x
    simp [hτ x]
  have hadd :
      ∑ x : α, (f x + f (τ x)) = ∑ x : α, f x + ∑ x : α, f (τ x) := by
    simpa using
      (Finset.sum_add_distrib (s := (Finset.univ : Finset α))
        (f := f) (g := fun x => f (τ x)))
  calc
    2 * ∑ x : α, f x = ∑ x : α, f x + ∑ x : α, f x := by ring
    _ = ∑ x : α, f x + ∑ x : α, f (τ x) := by rw [hsum]
    _ = ∑ x : α, (f x + f (τ x)) := by
      simpa using hadd.symm
    _ = ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
      refine Fintype.sum_congr (fun x : α => f x + f (τ x))
        (fun x : α => antisymmetricWeightContribution τ u y w score x) ?_
      intro x
      dsimp [f, signedScoreContribution, antisymmetricWeightContribution]
      rw [hu x, hy x, targetSign_flip]
      ring

/- A nonzero antisymmetric contribution must come from a point whose weight is
not invariant and whose score is nonzero. -/
omit [Fintype α] in
lemma weight_ne_and_score_ne_of_antisymmetricWeightContribution_ne_zero
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    {x : α}
    (hcontrib :
      antisymmetricWeightContribution τ u y w score x ≠ 0) :
    w x ≠ w (τ x) ∧ score (u x) ≠ 0 := by
  constructor
  · intro hw
    exact hcontrib (by simp [antisymmetricWeightContribution, hw])
  · intro hscore
    exact hcontrib (by simp [antisymmetricWeightContribution, hscore])

/-- If weights are symmetric at every nonzero-score point, the invariant soft
score has zero signed signal. -/
theorem signedScore_sum_eq_zero_of_score_support_weight_symmetric
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 := by
  classical
  let S : ℤ := ∑ x : α, signedScoreContribution u y w score x
  have hdecomp :
      2 * S =
        ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
    simpa [S] using
      two_mul_signedScore_sum_eq_antisymmetricWeight_sum
        τ u y w score hτ hu hy
  have hanti :
      (∑ x : α, antisymmetricWeightContribution τ u y w score x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hscore : score (u x) = 0
    · simp [antisymmetricWeightContribution, hscore]
    · have hw : w (τ x) = w x := hsym x hscore
      simp [antisymmetricWeightContribution, hw]
  have htwice : 2 * S = 0 := by
    rw [hdecomp, hanti]
  have hS : S = 0 := by
    omega
  simpa [S] using hS

/-- A nonzero invariant-score signal forces a concrete nonzero-score point
where the weighting is asymmetric across the involution. -/
theorem exists_weight_asymmetric_score_point_of_signedScore_sum_ne_zero
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 := by
  classical
  let S : ℤ := ∑ x : α, signedScoreContribution u y w score x
  have hsignalS : S ≠ 0 := by
    simpa [S] using hsignal
  have htwice : 2 * S ≠ 0 := by
    exact mul_ne_zero (by norm_num) hsignalS
  have hdecomp :
      2 * S =
        ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
    simpa [S] using
      two_mul_signedScore_sum_eq_antisymmetricWeight_sum
        τ u y w score hτ hu hy
  have hanti_ne :
      (∑ x : α, antisymmetricWeightContribution τ u y w score x) ≠ 0 := by
    intro hzero
    exact htwice (by rw [hdecomp, hzero])
  by_contra hnone
  have hanti_zero :
      (∑ x : α, antisymmetricWeightContribution τ u y w score x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_contra hcontrib
    have hx :=
      weight_ne_and_score_ne_of_antisymmetricWeightContribution_ne_zero
        τ u y w score hcontrib
    exact hnone ⟨x, hx⟩
  exact hanti_ne hanti_zero

end

end Mettapedia.Computability.PNP
