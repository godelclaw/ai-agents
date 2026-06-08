/-
# Bondy & Murty, Graph Theory — Chapter 1: Graphs

Formalization of definitions and results from Chapter 1 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

This chapter provides the foundational definitions. Many of these are
already available in Mathlib's `SimpleGraph` library.

## Contents
- Pointers to Mathlib for core graph definitions
- Graph operations: union, intersection, complement, join
- Handshaking lemma and parity of odd-degree vertices
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §1.1 — Definitions (pointers to Mathlib)

| Bondy–Murty           | Mathlib                                     |
|------------------------|---------------------------------------------|
| Simple graph           | `SimpleGraph V`                             |
| Vertex set             | `V`                                         |
| Edge set               | `G.edgeSet` / `G.edgeFinset`                |
| Order v(G)             | `Fintype.card V`                            |
| Size e(G)              | `G.edgeFinset.card`                         |
| Adjacency              | `G.Adj u v`                                 |
| Neighbourhood N(v)     | `G.neighborFinset v`                        |
| Degree d(v)            | `G.degree v`                                |
| k-regular              | `G.IsRegularOfDegree k`                     |
| Complete graph Kn      | `⊤ : SimpleGraph (Fin n)`                   |
| Complement Ḡ           | `Gᶜ`                                        |
| Subgraph                | `SimpleGraph.Subgraph`                     |
| Induced subgraph       | `G.induce S`                                |
| Isomorphism            | `G ≃g H`                                    |
-/

/-! ### Handshaking Lemma (Bondy–Murty, Theorem 1.1)

> "For any graph G, Σ d(v) = 2 · e(G)."

This is Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/

/-- **Theorem 1.1** (Handshaking Lemma): Σ d(v) = 2 |E|.
    (Bondy–Murty §1.2) -/
theorem handshaking_lemma :
    ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges G

/-- **Corollary 1.2**: The number of vertices of odd degree is even.
    (Bondy–Murty §1.2) -/
theorem even_odd_degree_vertices :
    Even (Finset.univ.filter fun v => Odd (G.degree v)).card :=
  SimpleGraph.even_card_odd_degree_vertices G

/-! ### Graph operations

Bondy–Murty define graph union, intersection, and complement. -/

/-- The **union** of two graphs on the same vertex type is the graph
    whose edges are the union of both edge sets. -/
def graphUnion (H : SimpleGraph V) : SimpleGraph V := G ⊔ H

/-- The **intersection** of two graphs on the same vertex type. -/
def graphIntersection (H : SimpleGraph V) : SimpleGraph V := G ⊓ H

end AutoBooks.GraphTheory.BondyMurty.Ch01
