/-
# Diestel, Graph Theory — Section 1.10: Other Notions of Graphs

Formalization of definitions from Section 1.10 of:
  R. Diestel, *Graph Theory* (5th edition), Springer GTM 173.

This section introduces directed graphs, multigraphs, and hypergraphs.
We provide definition pointers; these are largely separate from
Mathlib's `SimpleGraph` and serve as a definitional reference.

## Contents
- Pointers to Mathlib for digraphs (`Quiver`, `SimpleGraph.orientation`)
- Definitions of multigraph (bundled)
- Definitions of hypergraph (bundled)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Quiver.Basic

set_option linter.unusedSectionVars false

namespace AutoBooks.GraphTheory.Diestel.Ch01

/-! ### Diestel §1.10 — Other notions (pointers to Mathlib)

| Diestel               | Mathlib / Lean                              |
|-----------------------|---------------------------------------------|
| Directed graph        | `Quiver` (general), or `SimpleGraph` + orientation |
| Orientation of G      | `SimpleGraph.orientation` (partial Mathlib)  |
| Multigraph            | Not directly in Mathlib for `SimpleGraph`    |
| Hypergraph            | `SimpleHypergraph` (partial Mathlib)         |

Diestel's Section 1.10 is primarily definitional.  The formal content
below records the definitions for reference; no substantial theorems
are proved in this section of the textbook.
-/

/-- A **multigraph** on vertex type V with edge label type E. Each edge
    has two (not necessarily distinct) endpoints. Multiple edges between
    the same pair of vertices are allowed, as are loops. -/
structure Multigraph (V : Type*) (E : Type*) where
  endpts : E → V × V

/-- In a multigraph, vertex v has **degree** equal to the number of
    edge-endpoint incidences (loops count twice). -/
noncomputable def Multigraph.degree [DecidableEq V] [Fintype E]
    (M : Multigraph V E) (v : V) : ℕ :=
  (Finset.univ.filter fun e => (M.endpts e).1 = v).card +
  (Finset.univ.filter fun e => (M.endpts e).2 = v).card

/-- A **hypergraph** on vertex type V. Each hyperedge is a non-empty
    finite subset of V (generalising graphs, where |e| = 2). -/
structure Hypergraph (V : Type*) where
  edges : Set (Finset V)
  edge_nonempty : ∀ e ∈ edges, e.Nonempty

end AutoBooks.GraphTheory.Diestel.Ch01
