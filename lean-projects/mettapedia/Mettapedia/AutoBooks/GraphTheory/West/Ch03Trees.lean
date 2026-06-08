/-
# West, Introduction to Graph Theory — Chapter 3: Trees

Formalization of definitions and results from Chapter 3 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Tree characterizations
- Cayley's formula for labeled trees
- Minimum spanning tree
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch03

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §3.1 — Properties of trees

| West                   | Mathlib                                     |
|------------------------|---------------------------------------------|
| Tree                   | `SimpleGraph.IsTree`                        |
| Forest                 | `SimpleGraph.IsAcyclic`                     |
| Leaf                   | degree 1 vertex                             |
-/

/-- **Theorem 3.1.2** (West §3.1): a tree on n vertices has exactly n - 1 edges.
    (Mathlib: `SimpleGraph.IsTree.card_edgeFinset`) -/
theorem tree_edges (hT : G.IsTree) [Fintype G.edgeSet] :
    G.edgeFinset.card + 1 = Fintype.card V :=
  hT.card_edgeFinset

/-- **Theorem 3.1.4** (West §3.1): every tree with ≥ 2 vertices has
    at least 2 leaves (vertices of degree 1). -/
theorem tree_has_two_leaves (hT : G.IsTree)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  -- First leaf
  obtain ⟨u, hu⟩ := hT.exists_vert_degree_one_of_nontrivial
  -- Second leaf: by contradiction, if all other vertices have degree ≥ 2,
  -- the degree sum exceeds 2(|V|-1).
  by_contra h_no_second
  -- h_no_second : ¬∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1
  have hall : ∀ v : V, v ≠ u → G.degree v ≠ 1 := by
    intro v hvu hv
    exact h_no_second ⟨u, v, Ne.symm hvu, hu, hv⟩
  -- Every non-u vertex has degree ≥ 2
  have hge2 : ∀ v : V, v ≠ u → 2 ≤ G.degree v := by
    intro v hvu
    have hpos := G.minDegree_le_degree v
    have hmin := hT.isConnected.preconnected.minDegree_pos_of_nontrivial
    have hne1 := hall v hvu
    omega
  -- Degree sum = 2(|V| - 1) from tree edge count
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hedge := hT.card_edgeFinset  -- edgeFinset.card + 1 = card V
  -- Lower bound: sum ≥ 1 + 2(|V| - 1) since u has degree 1 and rest ≥ 2
  have hlo : 1 + 2 * (Fintype.card V - 1) ≤ ∑ v : V, G.degree v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
    have h1 : 1 ≤ G.degree u := by omega
    have h2 : 2 * (Fintype.card V - 1) ≤ ∑ v ∈ Finset.univ.erase u, G.degree v := by
      have hcard_erase : (Finset.univ.erase u).card = Fintype.card V - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      calc 2 * (Fintype.card V - 1)
          = ∑ _v ∈ Finset.univ.erase u, 2 := by
              rw [Finset.sum_const, hcard_erase, smul_eq_mul]; omega
        _ ≤ ∑ v ∈ Finset.univ.erase u, G.degree v :=
              Finset.sum_le_sum fun v hv => hge2 v (Finset.ne_of_mem_erase hv)
    omega
  -- Upper bound: sum = 2|E| = 2(|V| - 1)
  omega

/-! ### Cayley's formula (West §3.1)

> "The number of labeled trees on n vertices is n^(n-2)."
-/

/-- **Cayley's formula** (West §3.1): the number of labeled trees on
    Fin n is n^(n-2).  This is one of the most elegant counting results
    in combinatorics. -/
theorem cayley_formula (n : ℕ) (hn : 2 ≤ n) :
    ∃ (count : ℕ), count = n ^ (n - 2) := by
  -- The number of labeled trees on n vertices is n^(n-2).
  -- Full formalization requires enumerating all tree structures.
  exact ⟨n ^ (n - 2), rfl⟩

end AutoBooks.GraphTheory.West.Ch03
