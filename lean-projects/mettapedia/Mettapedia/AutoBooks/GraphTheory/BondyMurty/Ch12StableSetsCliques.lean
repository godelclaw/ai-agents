/-
# Bondy & Murty, Graph Theory — Chapter 12: Stable Sets and Cliques

Formalization of definitions and results from Chapter 12 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Ramsey's theorem (Theorem 12.6)
- Turán's theorem (Theorem 12.11)
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch09RamseyTheory
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch07ExtremalGraphTheory

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Theorem 12.6** (Ramsey 1930, Bondy–Murty §12.3): for any k, ℓ ≥ 1,
    there exists n such that every graph on n vertices contains either a
    k-clique or an ℓ-independent set. -/
theorem ramsey_bm (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    ∃ n, ∀ (H : SimpleGraph (Fin n)),
      (∃ S : Finset (Fin n), k ≤ S.card ∧ H.IsClique ↑S) ∨
      (∃ S : Finset (Fin n), ℓ ≤ S.card ∧ Hᶜ.IsClique ↑S) :=
  AutoBooks.GraphTheory.Diestel.Ch09.ramsey_finite k ℓ

/-- **Theorem 12.11** (Turán 1941, Bondy–Murty §12.4): ex(n, Kᵣ) is
    achieved by the Turán graph T(n, r-1). -/
theorem turan_bm (n r : ℕ) (hr : 2 ≤ r) (hn : r ≤ n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hcf : H.CliqueFree r) :
    H.edgeFinset.card ≤ n * n * (r - 2) / (2 * (r - 1)) :=
  AutoBooks.GraphTheory.Diestel.Ch07.turan_theorem n r hr hn H hcf

end AutoBooks.GraphTheory.BondyMurty.Ch12
