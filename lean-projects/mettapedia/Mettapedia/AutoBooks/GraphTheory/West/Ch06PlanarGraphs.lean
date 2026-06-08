/-
# West, Introduction to Graph Theory — Chapter 6: Planar Graphs

Formalization of definitions and results from Chapter 6 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Plane graphs and embeddings
- Euler's formula
- Kuratowski's theorem
- Planarity testing
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch04PlanarGraphs

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch06

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §6.1 — Embeddings and Euler's formula

A plane embedding of a graph draws vertices as points and edges as arcs
that intersect only at endpoints. Euler's formula relates vertices, edges,
and faces.
-/

/-- West's definition of planarity (via excluded minors). -/
def IsPlanar := AutoBooks.GraphTheory.Diestel.Ch04.IsPlanar G

/-- **Theorem 6.1.21** (Euler 1752, West §6.1): For a connected plane graph,
    n - m + f = 2 where n = |V|, m = |E|, and f = number of faces. -/
theorem euler_formula_west (hplanar : IsPlanar G) (hconn : G.Connected)
    (n m f : ℕ) (hn : n = Fintype.card V) (hm : m = G.edgeFinset.card)
    (hf : f = AutoBooks.GraphTheory.Diestel.Ch04.numFaces n m) :
    n + f = m + 2 :=
  AutoBooks.GraphTheory.Diestel.Ch04.euler_formula G hplanar hconn n m f hn hm hf

/-- **Corollary 6.1.22** (West §6.1): Planar graphs with n ≥ 3 have m ≤ 3n - 6. -/
theorem planar_edge_bound_west (hplanar : IsPlanar G) (hn : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
  AutoBooks.GraphTheory.Diestel.Ch04.planar_edge_bound G hplanar hn

/-- **Corollary 6.1.23** (West §6.1): Every planar graph has a vertex of degree ≤ 5. -/
theorem planar_has_small_degree (hplanar : IsPlanar G) (hne : Fintype.card V ≥ 1) :
    ∃ v : V, G.degree v ≤ 5 :=
  AutoBooks.GraphTheory.Diestel.Ch04.planar_has_small_degree_vertex G hplanar hne

/-! ### West §6.2 — Characterization of planar graphs -/

/-- **Theorem 6.2.2** (Kuratowski 1930, West §6.2): G is planar iff
    G has no subdivision of K₅ or K₃,₃. -/
theorem kuratowski_west :
    IsPlanar G ↔
      ¬AutoBooks.GraphTheory.Diestel.Ch04.IsTopologicalMinor (completeGraph (Fin 5)) G ∧
      ¬AutoBooks.GraphTheory.Diestel.Ch04.IsTopologicalMinor
        (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  AutoBooks.GraphTheory.Diestel.Ch04.kuratowski_theorem G

/-- K₅ is not planar. -/
theorem K5_not_planar_west : ¬IsPlanar (completeGraph (Fin 5)) :=
  AutoBooks.GraphTheory.Diestel.Ch04.K5_not_planar

/-- K₃,₃ is not planar. -/
theorem K33_not_planar_west : ¬IsPlanar (completeBipartiteGraph (Fin 3) (Fin 3)) :=
  AutoBooks.GraphTheory.Diestel.Ch04.K33_not_planar

/-! ### West §6.3 — Parameters of planarity -/

/-- **Proposition 6.3.3** (West §6.3): A planar graph is 5-colorable. -/
theorem planar_5colorable (hplanar : IsPlanar G) :
    G.Colorable 5 := by
  -- Follows from the fact that every planar graph has a vertex of degree ≤ 5
  -- and induction on |V|.
  sorry

/-- **The Four Color Theorem** (Appel–Haken 1976, West §6.3):
    Every planar graph is 4-colorable.

    Note: The machine-verified proof (Gonthier 2005) is in Coq.
    A Lean port would be a significant undertaking. -/
theorem four_color_theorem (hplanar : IsPlanar G) :
    G.Colorable 4 := by
  -- This requires substantial machinery beyond what is here.
  sorry

end AutoBooks.GraphTheory.West.Ch06
