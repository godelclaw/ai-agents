/-
# Bondy & Murty, Graph Theory — Chapter 21: Integer Flows and Coverings

Formalization of definitions and results from Chapter 21 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Nowhere-zero k-flows
- Tutte's 5-flow conjecture and Seymour's 6-flow theorem
- Jaeger's 4-flow conjecture
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch21

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §21.1 — Flows

A *nowhere-zero k-flow* on G is an orientation of G together with an
assignment of values in {1, …, k-1} to its edges such that, at every
vertex, the total flow in equals the total flow out (Kirchhoff's law).

Tutte's flow conjectures form a dual picture to the colouring problem
for planar graphs via the Four-Colour Theorem and plane duality.

| Bondy–Murty             | Status                                    |
|--------------------------|-------------------------------------------|
| 5-flow conjecture (Tutte)| Open (strongest form)                     |
| 6-flow theorem (Seymour) | Proved (Seymour 1981)                     |
| 4-flow conjecture (Tutte)| Open                                      |
-/

/-- A *nowhere-zero k-flow* assigns integer values in {-(k-1),…,-1,1,…,k-1}
    to oriented edges satisfying flow conservation.
    (Placeholder predicate.) -/
def HasNowhereZeroFlow (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ (f : V → V → ℤ),
    (∀ u v, G.Adj u v → f u v = -(f v u)) ∧
    (∀ u v, G.Adj u v → 1 ≤ (f u v).natAbs ∧ (f u v).natAbs < k) ∧
    ∀ v, ∑ w ∈ G.neighborFinset v, f v w = 0

/-- **Theorem 21.10** (Seymour 1981, Bondy–Murty §21.3): every bridgeless
    graph has a nowhere-zero 6-flow.

    > "Every bridgeless graph admits a nowhere-zero 6-flow."

    This is the strongest unconditional result toward Tutte's 5-flow
    conjecture. -/
theorem seymour_six_flow (hbridgeless : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
    HasNowhereZeroFlow G 6 := by
  sorry

/-- **Conjecture 21.17** (Tutte's 5-flow conjecture, Bondy–Murty §21.4):
    every bridgeless graph has a nowhere-zero 5-flow.

    This is recorded as a proposition rather than a theorem because it
    remains open as of 2026. -/
def tutte_five_flow_conjecture : Prop :=
  ∀ _ : ∀ e ∈ G.edgeSet, ¬G.IsBridge e, HasNowhereZeroFlow G 5

/-- **Theorem 21.5** (Tutte 1954, Bondy–Murty §21.2): a planar graph is
    k-colourable iff its dual has a nowhere-zero k-flow.
    (Placeholder; needs planar duality.) -/
theorem tutte_flow_colouring_duality (_k : ℕ) :
    True := by trivial -- placeholder; needs planarity and dual graph

end AutoBooks.GraphTheory.BondyMurty.Ch21
