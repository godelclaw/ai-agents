/-
# Bondy & Murty, Graph Theory — Chapter 10: Planar Graphs

Formalization of definitions and results from Chapter 10 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Euler's formula (Theorem 10.6)
- Kuratowski's theorem (Theorem 10.30)
- Edge bound for planar graphs (Corollary 10.8)
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch04PlanarGraphs

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch10

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Planarity as defined via Kuratowski characterization. -/
def IsPlanar := AutoBooks.GraphTheory.Diestel.Ch04.IsPlanar G

/-- **Theorem 10.6** (Euler's formula, Bondy–Murty §10.2): for a
    connected planar graph, |V| - |E| + |F| = 2. -/
theorem euler_formula_bm (hplanar : IsPlanar G) (hconn : G.Connected)
    (n m f : ℕ) (hn : n = Fintype.card V) (hm : m = G.edgeFinset.card)
    (hf : f = AutoBooks.GraphTheory.Diestel.Ch04.numFaces n m) :
    n + f = m + 2 :=
  AutoBooks.GraphTheory.Diestel.Ch04.euler_formula G hplanar hconn n m f hn hm hf

/-- **Corollary 10.8** (Bondy–Murty §10.2): a simple planar graph
    on n ≥ 3 vertices has at most 3n - 6 edges. -/
theorem planar_edge_bound_bm (hplanar : IsPlanar G) (hn : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
  AutoBooks.GraphTheory.Diestel.Ch04.planar_edge_bound G hplanar hn

/-- **Theorem 10.30** (Kuratowski 1930, Bondy–Murty §10.5): a graph is
    planar iff it contains no subdivision of K₅ or K₃,₃. -/
theorem kuratowski_bm :
    IsPlanar G ↔
      ¬AutoBooks.GraphTheory.Diestel.Ch04.IsTopologicalMinor (completeGraph (Fin 5)) G ∧
      ¬AutoBooks.GraphTheory.Diestel.Ch04.IsTopologicalMinor
        (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  AutoBooks.GraphTheory.Diestel.Ch04.kuratowski_theorem G

/-- K₅ is non-planar (Corollary 10.9). -/
theorem K5_not_planar_bm : ¬IsPlanar (completeGraph (Fin 5)) :=
  AutoBooks.GraphTheory.Diestel.Ch04.K5_not_planar

/-- K₃,₃ is non-planar (Corollary 10.11). -/
theorem K33_not_planar_bm : ¬IsPlanar (completeBipartiteGraph (Fin 3) (Fin 3)) :=
  AutoBooks.GraphTheory.Diestel.Ch04.K33_not_planar

end AutoBooks.GraphTheory.BondyMurty.Ch10
