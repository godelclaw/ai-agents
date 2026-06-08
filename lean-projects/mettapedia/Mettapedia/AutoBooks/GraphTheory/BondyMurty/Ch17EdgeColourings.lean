/-
# Bondy & Murty, Graph Theory — Chapter 17: Edge Colourings

Formalization of definitions and results from Chapter 17 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Edge chromatic number χ'(G) and edge colourings
- Theorem 17.4 (Vizing 1964): χ'(G) ≤ Δ(G) + 1
- Shannon's theorem (Theorem 17.2)
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch17

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §17.1 — Edge colourings

An *edge colouring* of G is an assignment of colours to edges such
that no two adjacent edges share a colour. The *edge chromatic number*
(or *chromatic index*) χ'(G) is the minimum number of colours needed.

| Bondy–Murty           | Notes                                       |
|------------------------|---------------------------------------------|
| Edge colouring         | proper colouring of the line graph          |
| χ'(G)                  | chromatic index                             |
| Class 1 / Class 2      | χ'(G) = Δ(G) / χ'(G) = Δ(G) + 1           |
-/

/-- An *edge colouring* with k colours: a map from edges to `Fin k`
    such that incident edges receive distinct colours. -/
def IsProperEdgeColouring (k : ℕ) (f : Sym2 V → Fin k) : Prop :=
  ∀ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
    e₁ ≠ e₂ → (∃ v : V, v ∈ e₁ ∧ v ∈ e₂) → f e₁ ≠ f e₂

/-- **Theorem 17.4** (Vizing 1964, Bondy–Murty §17.2): for any simple
    graph G, χ'(G) ≤ Δ(G) + 1.

    > "The edges of any simple graph G can be coloured with at most
    >  Δ(G) + 1 colours."

    This places every simple graph into Class 1 (χ' = Δ) or Class 2
    (χ' = Δ + 1). -/
theorem vizing_bm [Nonempty V] :
    ∃ f : Sym2 V → Fin (G.maxDegree + 1), IsProperEdgeColouring G _ f := by
  sorry

/-- **Theorem 17.2** (Shannon 1949, Bondy–Murty §17.1): for any
    multigraph, the edge chromatic number is at most ⌊3Δ/2⌋.
    (Stated here for simple graphs as χ'(G) ≤ ⌊3Δ/2⌋.) -/
theorem shannon_bm [Nonempty V] :
    ∃ f : Sym2 V → Fin (3 * G.maxDegree / 2 + 1),
      IsProperEdgeColouring G _ f := by
  sorry

end AutoBooks.GraphTheory.BondyMurty.Ch17
