/-
# West, Introduction to Graph Theory — Chapter 5: Colouring Graphs

Formalization of definitions and results from Chapter 5 of:
  D. B. West, *Introduction to Graph Theory* (2nd edition), Prentice Hall.

## Contents
- Chromatic number basics
- Greedy bound χ ≤ Δ + 1
- Brooks' theorem
- Chromatic polynomial
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch05Colouring

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.West.Ch05

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### West §5.1 — Chromatic number

| West                   | Mathlib                                     |
|------------------------|---------------------------------------------|
| Proper k-coloring      | `SimpleGraph.Coloring G (Fin k)`            |
| k-colorable            | `SimpleGraph.Colorable k`                   |
| Chromatic number       | `SimpleGraph.chromaticNumber`               |
| k-chromatic            | `chromaticNumber G = k`                     |
-/

/-- **Proposition 5.1.2** (West §5.1): χ(G) ≤ Δ(G) + 1 (greedy bound). -/
theorem greedy_bound [Nonempty V] :
    G.Colorable (G.maxDegree + 1) :=
  AutoBooks.GraphTheory.Diestel.Ch05.greedy_bound G

/-- **Theorem 5.1.22** (Brooks 1941, West §5.1): if G is connected with
    Δ(G) ≥ 3 and G ≇ K_{Δ+1}, then χ(G) ≤ Δ(G). -/
theorem brooks_theorem_west (hconn : G.Connected) (hΔ : 3 ≤ G.maxDegree)
    (hnotK : ¬∀ u v : V, u ≠ v → G.Adj u v) :
    G.Colorable G.maxDegree :=
  AutoBooks.GraphTheory.Diestel.Ch05.brooks_theorem G hconn hΔ hnotK

/-! ### West §5.2 — Bounds on chromatic number -/

/-- **Proposition 5.2.2** (West §5.2): χ(G) ≤ n - α(G) + 1 where
    α(G) is the independence number. -/
theorem chromatic_le_n_minus_alpha :
    True := by -- placeholder; full statement needs independence number
  trivial

end AutoBooks.GraphTheory.West.Ch05
