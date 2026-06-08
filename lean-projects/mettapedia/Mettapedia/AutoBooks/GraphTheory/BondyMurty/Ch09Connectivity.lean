/-
# Bondy & Murty, Graph Theory — Chapter 9: Connectivity

Formalization of definitions and results from Chapter 9 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Connectivity and edge-connectivity
- Theorem 9.1 (Whitney): κ(G) ≤ κ'(G) ≤ δ(G)
- Theorem 9.5 (Menger 1927, vertex version)
- Theorem 9.7 (Menger, edge version)
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch03Connectivity

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch09

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §9.1 — Connectivity

| Bondy–Murty           | Mathlib                                     |
|------------------------|---------------------------------------------|
| k-connected            | vertex connectivity (custom def)            |
| k-edge-connected       | `SimpleGraph.IsEdgeConnected k`             |
| κ(G)                   | vertex connectivity number                  |
| κ'(G)                  | edge connectivity number                    |
-/

/-- **Theorem 9.1** (Whitney inequality, Bondy–Murty §9.1):
    κ(G) ≤ κ'(G) ≤ δ(G).
    (Same as Diestel Proposition 1.4.2) -/
theorem whitney_inequality :
    True := by -- placeholder; see Diestel Ch01Sec04 for partial proof
  trivial

/-! ### Menger's theorem (Bondy–Murty §9.3)

> "For any two nonadjacent vertices a and b of a graph G, the
>  minimum number of vertices in an a-b separator equals the
>  maximum number of internally disjoint a-b paths."
-/

/-- **Theorem 9.5** (Menger 1927, vertex version, Bondy–Murty §9.3).

    The current formal wrapper reuses the live `Diestel.Ch03` statement.
    That shell still omits the pairwise-disjointness condition on the family
    of `A`-`B` paths, so it is weaker than the classical Menger theorem. -/
theorem menger_vertex_bm (A B : Finset V) :
    ∃ k : ℕ, (∀ S : Finset V,
      AutoBooks.GraphTheory.Diestel.Ch03.IsABSeparator G A B S → k ≤ S.card) ∧
      ∃ paths : Fin k → Σ (u v : V), G.Walk u v,
        (∀ i, (paths i).2.2.IsPath) ∧
        (∀ i, (paths i).1 ∈ A) ∧
        (∀ i, (paths i).2.1 ∈ B) :=
  AutoBooks.GraphTheory.Diestel.Ch03.menger_vertex (G := G) A B

/-- **Theorem 9.7** (Menger, edge version, Bondy–Murty §9.3):
    min |edge cut between a and b| = max |edge-disjoint a-b paths|. -/
theorem menger_edge_bm :
    True := by -- placeholder; see Diestel Ch03 for full statement
  trivial

end AutoBooks.GraphTheory.BondyMurty.Ch09
