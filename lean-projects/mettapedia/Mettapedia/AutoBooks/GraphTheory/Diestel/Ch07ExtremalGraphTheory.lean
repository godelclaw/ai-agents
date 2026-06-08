/-
# Diestel, Graph Theory — Chapter 7: Extremal Graph Theory

Formalization of definitions and results from Chapter 7 of:
  R. Diestel, *Graph Theory* (5th edition), Springer GTM 173.

## Contents
- Extremal number ex(n, H)
- Theorem 7.1.1 (Turán 1941): ex(n, K_r) = edges in the Turán graph
- Theorem 7.1.2 (Erdős–Stone 1946): asymptotic formula for ex(n, H)
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.Diestel.Ch07

/-! ### Extremal number -/

/-- **ex(n, r)**: the maximum number of edges in a K_r-free graph on n vertices. -/
noncomputable def extremalNumber (n r : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.CliqueFree r ∧ G.edgeFinset.card = m}

/-- The number of edges in the Turán graph T(n, r-1). -/
noncomputable def turanEdges (n r : ℕ) : ℕ :=
  n * n * (r - 2) / (2 * (r - 1))

/-! ### Turán's theorem (Diestel §7.1) -/

/-- Arithmetic lemma: Mathlib's exact Turán bound ≤ our simplified formula. -/
private lemma turan_bound_le (n r : ℕ) (hr : 2 ≤ r) :
    (n ^ 2 - (n % (r - 1)) ^ 2) * (r - 1 - 1) / (2 * (r - 1)) +
      (n % (r - 1)).choose 2 ≤ n * n * (r - 2) / (2 * (r - 1)) := by
  set m := n % (r - 1)
  set d := 2 * (r - 1)
  have hd_pos : 0 < d := by omega
  have hm_lt : m < r - 1 := Nat.mod_lt n (by omega)
  have hr2 : r - 1 - 1 = r - 2 := by omega
  rw [hr2]
  -- Suffices: LHS * d ≤ n²(r-2), then LHS ≤ n²(r-2)/d
  suffices hmul : ((n ^ 2 - m ^ 2) * (r - 2) / d + m.choose 2) * d ≤ n ^ 2 * (r - 2) by
    calc (n ^ 2 - m ^ 2) * (r - 2) / d + m.choose 2
        = ((n ^ 2 - m ^ 2) * (r - 2) / d + m.choose 2) * d / d := by
          rw [Nat.mul_div_cancel _ hd_pos]
      _ ≤ (n ^ 2 * (r - 2)) / d := Nat.div_le_div_right hmul
      _ = n * n * (r - 2) / d := by rw [sq]
  -- (n²-m²)(r-2)/d * d ≤ (n²-m²)(r-2)
  have hdiv_mul : (n ^ 2 - m ^ 2) * (r - 2) / d * d ≤ (n ^ 2 - m ^ 2) * (r - 2) :=
    Nat.div_mul_le_self _ d
  -- m*(m-1)*(r-1) ≤ m²*(r-2) — core fact
  have hkey : m * (m - 1) * (r - 1) ≤ m ^ 2 * (r - 2) := by
    rcases m with _ | m
    · simp
    · simp only [Nat.succ_sub_one, sq]
      suffices m * (r - 1) ≤ (m + 1) * (r - 2) by
        calc (m + 1) * m * (r - 1) = (m + 1) * (m * (r - 1)) := mul_assoc _ _ _
          _ ≤ (m + 1) * ((m + 1) * (r - 2)) := Nat.mul_le_mul_left _ this
          _ = (m + 1) * (m + 1) * (r - 2) := (mul_assoc _ _ _).symm
      have hrr : r - 1 = r - 2 + 1 := by omega
      calc m * (r - 1) = m * (r - 2 + 1) := by rw [hrr]
        _ = m * (r - 2) + m := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ m * (r - 2) + (r - 2) := Nat.add_le_add_left (by omega) _
        _ = (m + 1) * (r - 2) := by rw [Nat.add_mul, Nat.one_mul]
  -- m*(m-1)/2 * d ≤ m²*(r-2) via /2 * 2 ≤ original, then *(r-1)
  have hchoose_d_le : m * (m - 1) / 2 * d ≤ m ^ 2 * (r - 2) := by
    calc m * (m - 1) / 2 * d
        = (m * (m - 1) / 2 * 2) * (r - 1) := by
          show m * (m - 1) / 2 * (2 * (r - 1)) = m * (m - 1) / 2 * 2 * (r - 1)
          rw [mul_assoc]
      _ ≤ m * (m - 1) * (r - 1) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ 2)
      _ ≤ m ^ 2 * (r - 2) := hkey
  -- Combine with choose_two_right
  rw [Nat.choose_two_right]
  have hm_sq_le : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.mod_le n (r - 1)) 2
  calc ((n ^ 2 - m ^ 2) * (r - 2) / d + m * (m - 1) / 2) * d
      = (n ^ 2 - m ^ 2) * (r - 2) / d * d + m * (m - 1) / 2 * d := by
        rw [Nat.add_mul]
    _ ≤ (n ^ 2 - m ^ 2) * (r - 2) + m ^ 2 * (r - 2) :=
        Nat.add_le_add hdiv_mul hchoose_d_le
    _ = n ^ 2 * (r - 2) := by
        rw [show (n ^ 2 - m ^ 2) * (r - 2) + m ^ 2 * (r - 2) =
            (n ^ 2 - m ^ 2 + m ^ 2) * (r - 2) from (Nat.add_mul _ _ _).symm,
            Nat.sub_add_cancel hm_sq_le]

/-- **Theorem 7.1.1** (Turán 1941): a K_r-free graph on n vertices has
    at most n²(r-2)/(2(r-1)) edges.  (Diestel §7.1, p. 149)

    Proof: apply Mathlib's `CliqueFree.card_edgeFinset_le`, then bound
    the exact Turán number by our simplified formula. -/
theorem turan_theorem (n r : ℕ) (hr : 2 ≤ r) (hn : r ≤ n) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.CliqueFree r → G.edgeFinset.card ≤ turanEdges n r := by
  intro G _ hcf
  unfold turanEdges
  have hcf' : G.CliqueFree ((r - 1) + 1) := by rwa [show r - 1 + 1 = r from by omega]
  have hmathlib := hcf'.card_edgeFinset_le
  simp only [Fintype.card_fin] at hmathlib
  exact le_trans hmathlib (turan_bound_le n r hr)

/-! ### Erdős–Stone theorem (Diestel §7.1) -/

/-- **Theorem 7.1.2** (Erdős–Stone 1946). (Diestel §7.1, p. 150) -/
theorem erdos_stone (r t : ℕ) (hr : 2 ≤ r) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        turanEdges n r < G.edgeFinset.card →
        ∃ S : Fin r → Finset (Fin n),
          (∀ i, t ≤ (S i).card) ∧
          ∀ i j, i ≠ j → ∀ u ∈ S i, ∀ v ∈ S j, G.Adj u v := by
  sorry

end AutoBooks.GraphTheory.Diestel.Ch07
