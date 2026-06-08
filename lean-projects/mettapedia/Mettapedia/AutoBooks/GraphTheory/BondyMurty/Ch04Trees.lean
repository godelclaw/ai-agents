/-
# Bondy & Murty, Graph Theory — Chapter 4: Trees

Formalization of definitions and results from Chapter 4 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Tree characterizations
- Theorem 4.1: equivalent conditions for trees
- Theorem 4.3: number of edges in a tree
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch04

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §4.1 — Trees

Trees are connected acyclic graphs. Mathlib defines `SimpleGraph.IsTree`.
-/

/-- **Theorem 4.1** (Bondy–Murty §4.1): equivalent characterizations of trees.
    A connected graph is a tree iff any two vertices are joined by a unique path.
    (Mathlib: `isTree_iff_existsUnique_path`) -/
theorem tree_iff_unique_path :
    G.IsTree ↔ Nonempty V ∧ ∀ u v : V, ∃! p : G.Walk u v, p.IsPath :=
  isTree_iff_existsUnique_path

/-- **Theorem 4.3** (Bondy–Murty §4.1): a tree on n vertices has n - 1 edges.
    (Mathlib: `SimpleGraph.IsTree.card_edgeFinset`) -/
theorem tree_edge_count [Fintype G.edgeSet] (hT : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  hT.card_edgeFinset

end AutoBooks.GraphTheory.BondyMurty.Ch04
