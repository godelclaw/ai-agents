/-
# West, Introduction to Graph Theory — Chapter 7: Matroids

Formalization of definitions from Chapter 7 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Matroid definition and basic properties
- Graphic matroid (cycle matroid of a graph)
- Matroid duality
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.unusedSectionVars false

open SimpleGraph

namespace AutoBooks.GraphTheory.West.Ch07

/-! ### West §7.1 — Matroid definition

A **matroid** M = (S, I) consists of a finite ground set S and a
collection I of subsets of S (independent sets) satisfying:
1. ∅ ∈ I
2. If B ∈ I and A ⊆ B, then A ∈ I (hereditary)
3. If A, B ∈ I with |A| < |B|, then ∃ x ∈ B \ A, A ∪ {x} ∈ I (exchange)

Matroids generalize graph forests: the independent sets of the
*graphic matroid* of a graph G are the acyclic edge sets (forests).

See also Mathlib's `Matroid` type in `Mathlib.Order.SetPartition.Matroid`.
-/

/-- The **graphic matroid** (cycle matroid) of a graph has edge sets
    as ground set and forests as independent sets. The bases are
    spanning forests. -/
def graphicMatroidIndependent (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) : Prop :=
  F ⊆ G.edgeFinset ∧
  (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsAcyclic

end AutoBooks.GraphTheory.West.Ch07
