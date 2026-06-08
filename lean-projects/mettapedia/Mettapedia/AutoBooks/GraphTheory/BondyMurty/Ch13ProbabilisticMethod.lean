/-
# Bondy & Murty, Graph Theory — Chapter 13: The Probabilistic Method

Formalization of definitions and results from Chapter 13 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Ramsey lower bound R(k,k) > 2^(k/2) (Erdős 1947)
- Property B of hypergraphs
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

set_option linter.unusedSectionVars false

/-! ## Infrastructure: Counting SimpleGraphs

The number of simple graphs on n vertices is 2^(n choose 2), since each of the
(n choose 2) unordered pairs can independently be an edge or not. -/

section GraphCounting

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- Given a set of off-diagonal elements of Sym2 V, construct a simple graph. -/
def SimpleGraph.ofEdgeSubset (s : Set {e : Sym2 V // ¬e.IsDiag}) : SimpleGraph V where
  Adj x y := ∃ h : ¬(s(x, y)).IsDiag, ⟨s(x, y), h⟩ ∈ s
  symm x y := by simp only [Sym2.eq_swap]; exact id
  loopless := ⟨fun x ⟨h, _⟩ => h (Sym2.mk_isDiag_iff.mpr rfl)⟩

/-- SimpleGraph V is equivalent to subsets of off-diagonal Sym2 V. -/
def SimpleGraph.equivOffDiagSubsets :
    SimpleGraph V ≃ Set {e : Sym2 V // ¬e.IsDiag} where
  toFun G e := e.val ∈ G.edgeSet
  invFun := SimpleGraph.ofEdgeSubset V
  left_inv G := by
    ext x y
    show (∃ h : ¬s(x, y).IsDiag, G.Adj x y) ↔ G.Adj x y
    constructor
    · intro ⟨_, h⟩; exact h
    · intro h; exact ⟨G.not_isDiag_of_mem_edgeSet h, h⟩
  right_inv s := by
    ext ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      show (∃ h : ¬s(x, y).IsDiag, ⟨s(x, y), h⟩ ∈ s) ↔ ⟨s(x, y), he⟩ ∈ s
      constructor
      · intro ⟨_, h⟩; exact h
      · intro h; exact ⟨he, h⟩

/-- SimpleGraph V corresponds to choosing which unordered pairs are edges.
    Since there are (n choose 2) such pairs, there are 2^(n choose 2) graphs. -/
theorem card_simpleGraph :
    Fintype.card (SimpleGraph V) = 2 ^ (Fintype.card V).choose 2 := by
  rw [← Sym2.card_subtype_not_diag (α := V)]
  rw [← Fintype.card_set (α := {e : Sym2 V // ¬e.IsDiag})]
  exact Fintype.card_congr (SimpleGraph.equivOffDiagSubsets V)

end GraphCounting

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch13

/-! ### Bondy–Murty §13.1 — The probabilistic method

> "If the probability that a random structure has a certain property
>  is positive, then a structure with that property exists."

This principle, pioneered by Erdős, gives non-constructive existence
proofs for combinatorial objects. -/

/-- Cycle graph on n ≥ 3 vertices has degree exactly 2. -/
lemma cycleGraph_degree_eq_two (n : ℕ) (hn : 3 ≤ n) (v : Fin n) :
    (cycleGraph n).degree v = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact cycleGraph_degree_three_le

/-- Cycle graph is CliqueFree k for k ≥ 4. -/
lemma cycleGraph_cliqueFree_of_ge_four (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : 4 ≤ k) :
    (cycleGraph n).CliqueFree k := by
  -- A k-clique requires each vertex to have k-1 neighbors in the clique.
  -- But cycleGraph has degree 2, so can't have k ≥ 4 clique.
  intro s ⟨hs_clique, hs_card⟩
  -- In a k-clique, each vertex has k-1 neighbors within the clique.
  -- If k ≥ 4, then k-1 ≥ 3 > 2 = degree in cycleGraph.
  -- This contradicts degree bound.
  have hs_pos : 0 < s.card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hs_pos
  -- v ∈ s has ≥ k-1 neighbors in s (the other clique members)
  have h_deg_in_clique : k - 1 ≤ ((cycleGraph n).neighborFinset v ∩ s).card := by
    -- All other members of s are neighbors of v (clique property)
    have hsub : s \ {v} ⊆ (cycleGraph n).neighborFinset v := by
      intro w hw
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      -- hs_clique : (↑s : Set _).Pairwise (cycleGraph n).Adj
      -- We need: v ∈ ↑s, w ∈ ↑s, v ≠ w → Adj v w
      have hv' : v ∈ (↑s : Set (Fin n)) := hv
      have hw' : w ∈ (↑s : Set (Fin n)) := hw.1
      have hne : v ≠ w := fun h => hw.2 h.symm
      exact hs_clique hv' hw' hne
    have h1 : s \ {v} ⊆ (cycleGraph n).neighborFinset v ∩ s := by
      intro x hx
      rw [Finset.mem_inter]
      exact ⟨hsub hx, (Finset.mem_sdiff.mp hx).1⟩
    have hsing : {v} ⊆ s := Finset.singleton_subset_iff.mpr hv
    have h_sdiff : (s \ {v}).card = k - 1 := by
      rw [Finset.card_sdiff_of_subset hsing, hs_card, Finset.card_singleton]
    calc k - 1 = (s \ {v}).card := h_sdiff.symm
      _ ≤ ((cycleGraph n).neighborFinset v ∩ s).card := Finset.card_le_card h1
  have h_deg_bound : ((cycleGraph n).neighborFinset v ∩ s).card ≤ (cycleGraph n).degree v :=
    Finset.card_le_card Finset.inter_subset_left
  have h_deg : (cycleGraph n).degree v = 2 := cycleGraph_degree_eq_two n hn v
  omega

/-- In cycleGraph n (for n ≥ 3), any independent set has size at most n/2.
    Proof: consecutive vertices are adjacent, so we can pick at most every other vertex. -/
lemma cycleGraph_indepSet_card_le_half (n : ℕ) (hn : 3 ≤ n) (s : Finset (Fin n))
    (hs : (cycleGraph n).IsIndepSet s) : s.card ≤ n / 2 := by
  -- For any v ∈ s, v+1 ∉ s (since v adj v+1 in cycleGraph and s is independent)
  -- Use pigeonhole: if |s| > n/2, then s and s+1 (shift) overlap
  by_contra h_gt
  push_neg at h_gt
  -- Define the successor function on Fin n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  let succ : Fin (m + 3) → Fin (m + 3) := (· + 1)
  have hsucc_inj : Function.Injective succ := fun a b h => by
    simp only [succ] at h
    have := congrArg (· - 1) h
    simp at this
    exact this
  let s' : Finset (Fin (m + 3)) := s.map ⟨succ, hsucc_inj⟩
  have hs'_card : s'.card = s.card := Finset.card_map _
  have h_sum : s.card + s'.card > Fintype.card (Fin (m + 3)) := by
    rw [hs'_card, Fintype.card_fin]; omega
  -- By pigeonhole, s ∩ s' ≠ ∅
  have h_inter : (s ∩ s').Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have h_disj : Disjoint s s' := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
    have h_union : (s ∪ s').card = s.card + s'.card :=
      Finset.card_union_of_disjoint h_disj
    have h_le : (s ∪ s').card ≤ Fintype.card (Fin (m + 3)) := Finset.card_le_univ _
    omega
  -- Get w ∈ s ∩ s'
  obtain ⟨w, hw_inter⟩ := h_inter
  rw [Finset.mem_inter, Finset.mem_map] at hw_inter
  obtain ⟨hw_s, v, hv_s, hvw⟩ := hw_inter
  -- w = succ v = v + 1 and w ∈ s, v ∈ s
  -- v and v+1 are both in s, but they're adjacent in cycleGraph
  simp only [Function.Embedding.coeFn_mk, succ] at hvw
  -- Now hvw : v + 1 = w
  have hv1_s : v + 1 ∈ s := hvw.symm ▸ hw_s
  have hadj : (cycleGraph (m + 3)).Adj v (v + 1) := by
    rw [cycleGraph_adj]
    right
    simp
  -- This contradicts independence (v and v+1 adjacent but both in independent set)
  have hne : v ≠ v + 1 := by simp
  have := hs hv_s hv1_s hne
  exact this hadj

/-- Corollary: cycleGraph n is (n/2 + 1)-independent-set-free. -/
lemma cycleGraph_indepSetFree (n : ℕ) (hn : 3 ≤ n) :
    (cycleGraph n).IndepSetFree (n / 2 + 1) := by
  intro s ⟨hs_indep, hs_card⟩
  have h_le := cycleGraph_indepSet_card_le_half n hn s hs_indep
  omega

/-- IndepSetFree is monotone: if G has no m-indep set and m ≤ k, then G has no k-indep set. -/
lemma IndepSetFree.mono {G : SimpleGraph α} {m k : ℕ} (h : G.IndepSetFree m) (hmk : m ≤ k) :
    G.IndepSetFree k := by
  intro s ⟨hs_indep, hs_card⟩
  -- s is a k-indep set. Take an m-element subset t ⊆ s.
  have hm_le : m ≤ s.card := by omega
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hm_le
  -- t is an m-indep set (subset of indep set is indep)
  have ht_indep : G.IsIndepSet t := by
    intro x hx y hy hxy
    exact hs_indep (ht_sub hx) (ht_sub hy) hxy
  exact h t ⟨ht_indep, ht_card⟩

/-! ### Supporting lemmas for probabilistic counting -/

/-- Key inequality: For n ≥ k ≥ 3, we have 2 × C(n,k) < n^k when k! > 2.
    Proof: C(n,k) * k! = descFactorial ≤ n^k, so C(n,k) * 2 < C(n,k) * k! ≤ n^k. -/
lemma two_mul_choose_lt_pow (n k : ℕ) (hn : k ≤ n) (hk : 3 ≤ k) :
    2 * n.choose k < n ^ k := by
  have h_desc := Nat.descFactorial_le_pow n k
  rw [← Nat.descFactorial_eq_factorial_mul_choose] at h_desc
  have h_fact := factorial_gt_two k hk
  have h_choose_pos := Nat.choose_pos hn
  calc 2 * n.choose k
      < k.factorial * n.choose k := by
        rw [mul_comm 2 _, mul_comm k.factorial _]
        exact Nat.mul_lt_mul_of_pos_right h_fact h_choose_pos
    _ = n.descFactorial k := Nat.descFactorial_eq_factorial_mul_choose _ _
    _ ≤ n ^ k := h_desc

/-- For k ≥ 3, k! > 2. This is the key inequality for the Ramsey lower bound. -/
lemma factorial_gt_two (k : ℕ) (hk : 3 ≤ k) : 2 < k.factorial := by
  have h3 : (3 : ℕ).factorial = 6 := by decide
  calc 2 < 6 := by decide
    _ = (3 : ℕ).factorial := h3.symm
    _ ≤ k.factorial := Nat.factorial_le hk

/-- The number of k-element subsets of an n-element set is n choose k. -/
lemma card_powersetCard_eq_choose (n k : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard k).card = n.choose k := by
  simp [Finset.card_powersetCard, Fintype.card_fin]

/-- Key exponent identity: for n = 2^m, we have n^k = 2^(m*k). -/
lemma pow_pow_eq (m k : ℕ) : (2 ^ m) ^ k = 2 ^ (m * k) := by
  rw [← Nat.pow_mul]

/-- For the Ramsey bound: (k choose 2) = k*(k-1)/2. -/
lemma choose_two_eq (k : ℕ) : k.choose 2 = k * (k - 1) / 2 := by
  rw [Nat.choose_two_right]

/-- For n = 2^m, we have n^k = 2^(m*k). When m = (k-1)/2, this gives n^k = 2^(k choose 2). -/
lemma pow_of_pow_two_eq (m k : ℕ) : (2 ^ m) ^ k = 2 ^ (m * k) := by
  rw [← Nat.pow_mul]

/-- Key identity for Ramsey: when n = 2^((k-1)/2), we have 2×C(n,k) < 2^(k choose 2). -/
lemma two_mul_choose_lt_pow_two_choose_two (k : ℕ) (hk : 3 ≤ k) :
    2 * (2 ^ ((k - 1) / 2)).choose k < 2 ^ (k.choose 2) := by
  set n := 2 ^ ((k - 1) / 2)
  set m := (k - 1) / 2
  have hn : n = 2 ^ m := rfl
  calc 2 * n.choose k
      < n ^ k := two_mul_choose_lt_pow_of_pow_two m k hk
    _ = 2 ^ (m * k) := pow_of_pow_two_eq m k
    _ ≤ 2 ^ (k.choose 2) := by
        -- Need: m * k ≤ k choose 2 = k * (k-1) / 2
        -- m = (k-1)/2, so m * k = (k-1)/2 * k ≤ k * (k-1) / 2
        -- This holds by commutativity when (k-1)/2 * k = k * (k-1) / 2
        apply Nat.pow_le_pow_right (by omega)
        rw [Nat.choose_two_right]
        -- m * k ≤ k * (k-1) / 2
        -- When k is odd: k - 1 is even, so (k-1)/2 * k = k * (k-1) / 2
        -- When k is even: (k-1)/2 is truncated, so (k-1)/2 * k ≤ k * (k-1) / 2
        have h_div_mul : (k - 1) / 2 * k ≤ k * (k - 1) / 2 := by
          rw [mul_comm k _, mul_comm _ k]
          exact Nat.div_mul_le_self (k - 1) 2

/-- **Theorem 13.2** (Erdős 1947, Bondy–Murty §13.1): R(k,k) > 2^((k-1)/2)
    for k ≥ 3.  That is, there exists a graph on n = 2^((k-1)/2) vertices
    with no k-clique and no k-independent set. -/
theorem ramsey_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      n = 2 ^ ((k - 1) / 2) ∧
      G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  set n := 2 ^ ((k - 1) / 2)
  -- When n < k, any graph works (CliqueFree holds by cardinality)
  by_cases hn : n < k
  · -- Easy case: n < k, so |Fin n| < k, both G and Gᶜ are trivially k-clique-free
    refine ⟨n, ⊥, rfl, ?_, ?_⟩
    · exact cliqueFree_of_card_lt (by simp only [Fintype.card_fin]; exact hn)
    · exact cliqueFree_of_card_lt (by simp only [Fintype.card_fin]; exact hn)
  · -- Hard case: n ≥ k. Use cycle graphs for k ≤ 10, sorry for k ≥ 11.
    push_neg at hn
    -- First show k ≥ 7 (k ≤ 6 implies n < k, contradiction)
    have hk_ge7 : 7 ≤ k := by
      by_contra h; push_neg at h
      -- k ∈ {3,4,5,6}, compute n for each case
      have : n < k := by
        have hk6 : k ≤ 6 := by omega
        -- For k = 3,4: (k-1)/2 = 1, n = 2
        -- For k = 5,6: (k-1)/2 = 2, n = 4
        have h1 : (k - 1) / 2 ≤ 2 := by omega
        have hn_le : n ≤ 4 := calc n = 2 ^ ((k - 1) / 2) := rfl
          _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) h1
          _ = 4 := by decide
        -- n ≤ 4 and k ≥ 3. When k ≥ 5, n ≤ 4 < k.
        -- When k ∈ {3,4}, (k-1)/2 ≤ 1 so n ≤ 2 < k.
        by_cases hk5 : k < 5
        · -- k ∈ {3, 4}, so (k-1)/2 ≤ 1, n ≤ 2
          have h2 : (k - 1) / 2 ≤ 1 := by omega
          have hn2 : n ≤ 2 := calc n = 2 ^ ((k - 1) / 2) := rfl
            _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) h2
            _ = 2 := by decide
          omega
        · -- k ∈ {5, 6}, n ≤ 4 < 5 ≤ k
          omega
      omega
    -- Now k ≥ 7. Use cycle graphs for k ≤ 10.
    by_cases hk_le10 : k ≤ 10
    · -- k ∈ {7,8,9,10}, use cycleGraph n
      have hn_ge3 : 3 ≤ n := by
        have h1 : 3 ≤ (k - 1) / 2 := by omega
        calc n = 2 ^ ((k - 1) / 2) := rfl
          _ ≥ 2 ^ 3 := Nat.pow_le_pow_right (by omega) h1
          _ ≥ 3 := by decide
      refine ⟨n, cycleGraph n, rfl, ?_, ?_⟩
      · -- cycleGraph n is k-clique-free (it's triangle-free, k ≥ 4)
        exact cycleGraph_cliqueFree_of_ge_four n hn_ge3 k (by omega)
      · -- (cycleGraph n)ᶜ is k-clique-free ↔ cycleGraph n is k-indep-free
        rw [cliqueFree_compl]
        -- Need: n/2 + 1 ≤ k
        have hk_gt_half : n / 2 + 1 ≤ k := by
          -- For k ∈ {7,8}: n = 8, n/2 + 1 = 5 ≤ 7,8
          -- For k ∈ {9,10}: n = 16, n/2 + 1 = 9 ≤ 9,10
          by_cases hk_lt9 : k < 9
          · -- k ∈ {7, 8}, n = 8
            have hn8 : n = 8 := by
              have h1 : (k - 1) / 2 = 3 := by omega
              simp only [n, h1]; decide
            omega
          · -- k ∈ {9, 10}, n = 16
            have hn16 : n = 16 := by
              have h1 : (k - 1) / 2 = 4 := by omega
              simp only [n, h1]; decide
            omega
        exact IndepSetFree.mono (cycleGraph_indepSetFree n hn_ge3) hk_gt_half
    · -- k ≥ 11, need probabilistic counting argument
      push_neg at hk_le10
      -- PROBABILISTIC METHOD (Erdős 1947):
      -- Total graphs on n vertices: 2^(n choose 2)
      -- Graphs with some k-clique: ≤ C(n,k) × 2^((n choose 2) - (k choose 2))
      -- Similarly for k-independent set
      -- If bad < total, good graphs exist.
      --
      -- Key bound: 2 × C(n,k) < 2^(k choose 2) when k! > 2.
      -- For k ≥ 3, k! ≥ 6 > 2, so the bound holds.
      --
      -- The counting argument:
      -- 1. For a fixed k-subset S, graphs where S is a clique: 2^((n choose 2) - (k choose 2))
      --    (the edges within S are determined, the rest are free)
      -- 2. Union bound: bad ≤ 2 × C(n,k) × 2^((n choose 2) - (k choose 2))
      -- 3. bad < total iff 2 × C(n,k) < 2^(k choose 2)
      -- 4. C(n,k) ≤ n^k / k! for any n, k
      -- 5. For n = 2^((k-1)/2): n^k = 2^(k(k-1)/2) = 2^(k choose 2)
      -- 6. So 2 × C(n,k) ≤ 2 × 2^(k choose 2) / k! = 2^(k choose 2 + 1) / k!
      -- 7. Need: 2^(k choose 2 + 1) / k! < 2^(k choose 2), i.e., 2 < k!
      -- 8. k ≥ 3 implies k! ≥ 6 > 2. QED.
      --
      -- The formalization of this counting argument requires:
      -- (a) Fintype instance for k-subsets of Fin n
      -- (b) Cardinality of graphs with fixed clique
      -- (c) The union bound via Finset.card_biUnion
      -- (d) Binomial inequality C(n,k) ≤ n^k / k!
      -- (e) Factorial inequality k! > 2 for k ≥ 3
      --
      -- This is standard combinatorics but requires careful Fintype bookkeeping.
      -- The key lemma `card_simpleGraph` (proved above) gives the total count.
      -- For now, we use sorry noting this is a well-known result from Erdős 1947.
      sorry

end AutoBooks.GraphTheory.BondyMurty.Ch13
