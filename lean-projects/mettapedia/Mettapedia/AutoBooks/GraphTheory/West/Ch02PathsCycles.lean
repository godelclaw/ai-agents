/-
# West, Introduction to Graph Theory — Chapter 2: Paths and Cycles

Formalization of definitions and results from Chapter 2 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Connections between vertices
- Bipartite characterization
- Euler circuits and trails
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch01Sec06Bipartite
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch01Sec08EulerTours

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch02

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §2.1 — Connectivity -/

/-- **Theorem 2.1.1** (König): A graph is bipartite iff it has no odd cycle.
    (West §2.1)

    Proved in Diestel §1.6 as `isBipartite_iff_no_odd_cycle`. -/
theorem bipartite_iff_no_odd_cycle :
    G.IsBipartite ↔ ¬AutoBooks.GraphTheory.Diestel.Ch01.HasOddCycle G :=
  AutoBooks.GraphTheory.Diestel.Ch01.isBipartite_iff_no_odd_cycle G

/-! ### West Theorem 2.1.3 — Euler's theorem

> "A graph G is Eulerian iff it has at most one nontrivial component
>  and every vertex has even degree."

Note: the standard iff needs a nonempty-edges condition for the ←
direction (a single vertex with no edges has all even degrees but no
Euler circuit, since `IsCircuit` requires a non-nil walk). -/

/-- **Theorem 2.1.3, sufficiency** (West §2.1):
    A connected graph with nonempty edges and all even degrees is Eulerian.
    Proved in Diestel §1.8 as `connected_even_degree_isEulerian`. -/
theorem euler_circuit_of_connected_even
    (hconn : G.Connected) (heven : ∀ v : V, Even (G.degree v))
    (hedge : G.edgeSet.Nonempty) :
    AutoBooks.GraphTheory.Diestel.Ch01.IsEulerian G :=
  AutoBooks.GraphTheory.Diestel.Ch01.connected_even_degree_isEulerian G hconn heven hedge

/-- **Theorem 2.1.3, necessity** (West §2.1):
    An Eulerian graph has all even degrees.
    Proved in Diestel §1.8 as `IsEulerian.all_even_degree`. -/
theorem euler_circuit_implies_even
    (h : AutoBooks.GraphTheory.Diestel.Ch01.IsEulerian G) :
    ∀ v : V, Even (G.degree v) :=
  AutoBooks.GraphTheory.Diestel.Ch01.IsEulerian.all_even_degree G h

end AutoBooks.GraphTheory.West.Ch02
