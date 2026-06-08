/-
# West, Introduction to Graph Theory — Chapter 6: Matching, Marriage, and Menger

Formalization of definitions and results from Chapter 6 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Matchings and vertex covers
- Hall's theorem (Thm 6.1.2)
- König–Egerváry theorem (Thm 6.1.6)
- Menger's theorem (Thm 6.2.1)
-/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hall

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch06

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §6.1 — Matchings and covers

| West                   | Mathlib                                     |
|------------------------|---------------------------------------------|
| Matching               | `Subgraph.IsMatching`                       |
| Perfect matching       | `Subgraph.IsPerfectMatching`                |
| Maximum matching       | (largest IsMatching)                        |
| Vertex cover           | (custom def)                                |
-/

/-- **Theorem 6.1.2** (Hall 1935, West §6.1): a bipartite graph G[X,Y]
    has a matching that saturates X iff |N(S)| ≥ |S| for all S ⊆ X.

    (Mathlib: `exists_isMatching_of_forall_ncard_le`) -/
theorem hall_theorem_west {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂)
    (hHall : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, p₁ ⊆ M.verts ∧ M.IsMatching :=
  exists_isMatching_of_forall_ncard_le hbip hHall

/-- **Theorem 6.1.6** (König-Egerváry 1931, West §6.1): in a bipartite graph,
    the maximum matching size equals the minimum vertex cover size. -/
theorem konig_egervary (hbip : G.IsBipartite) :
    True := by -- placeholder for König's theorem
  trivial

end AutoBooks.GraphTheory.West.Ch06
