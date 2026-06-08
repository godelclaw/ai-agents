/-
# Bondy & Murty, Graph Theory — Chapter 18: Hamilton Cycles

Formalization of definitions and results from Chapter 18 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Necessary conditions for Hamiltonicity
- Theorem 18.1 (Dirac 1952): δ ≥ n/2 ⟹ Hamiltonian
- Theorem 18.2 (Ore 1960): degree-sum condition
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch10HamiltonCycles

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch18

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Theorem 18.1** (Dirac 1952, Bondy–Murty §18.1): if |V| ≥ 3 and
    δ(G) ≥ ⌈|V|/2⌉, then G is Hamiltonian.

    Cross-references Diestel Ch10. -/
theorem dirac_bm (hn : 3 ≤ Fintype.card V)
    (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    G.IsHamiltonian :=
  AutoBooks.GraphTheory.Diestel.Ch10.dirac_theorem G hn hδ

/-- **Theorem 18.2** (Ore 1960, Bondy–Murty §18.1): if |V| ≥ 3 and
    d(u) + d(v) ≥ |V| for every non-adjacent pair, then G is Hamiltonian.

    Cross-references Diestel Ch10. -/
theorem ore_bm (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian :=
  AutoBooks.GraphTheory.Diestel.Ch10.ore_theorem G hn hore

end AutoBooks.GraphTheory.BondyMurty.Ch18
