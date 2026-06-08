/-
# West, Introduction to Graph Theory — Chapter 1: Definitions and Examples

Formalization of definitions and results from Chapter 1 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Pointers to Mathlib for core definitions
- Handshaking Lemma (Theorem 1.1)
- Degree-sum corollary (Corollary 1.2)
- Petersen graph and basic examples
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §1.1 — Definitions (pointers to Mathlib)

| West                   | Mathlib                                     |
|------------------------|---------------------------------------------|
| Simple graph           | `SimpleGraph V`                             |
| Adjacency              | `G.Adj u v`                                 |
| Degree d(v)            | `G.degree v`                                |
| Regular graph          | `G.IsRegularOfDegree k`                     |
| Complete graph Kn      | `⊤ : SimpleGraph (Fin n)`                   |
| Bipartite graph        | `G.IsBipartite`                             |
| Complement Ḡ           | `Gᶜ`                                        |
| Subgraph               | `SimpleGraph.Subgraph`                      |
-/

/-! ### Theorem 1.1 — Handshaking Lemma

> "If G is a graph, then Σ d(v) = 2|E(G)|."

This is the degree-sum formula. -/

/-- **Theorem 1.1** (Handshaking Lemma): Σ d(v) = 2 |E|.
    (West §1.1) -/
theorem thm_1_1_handshaking :
    ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges G

/-- **Corollary 1.2**: The number of vertices of odd degree is even.
    (West §1.1) -/
theorem cor_1_2_even_odd_degree :
    Even (Finset.univ.filter fun v => Odd (G.degree v)).card :=
  SimpleGraph.even_card_odd_degree_vertices G

/-! ### Example: Petersen graph

The **Petersen graph** K(5,2) has as vertices the 2-element subsets of
{0,1,2,3,4}; two vertices are adjacent iff they are disjoint.
It is 3-regular, has 10 vertices, 15 edges, girth 5, diameter 2,
and is not Hamiltonian.

See also Mathlib's Kneser graph infrastructure. -/

end AutoBooks.GraphTheory.West.Ch01
