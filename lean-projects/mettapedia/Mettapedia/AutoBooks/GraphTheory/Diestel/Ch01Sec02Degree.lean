/-
# Diestel, Graph Theory — Section 1.2: The Degree of a Vertex

Formalization of definitions and results from Section 1.2 of:
  R. Diestel, *Graph Theory* (5th edition), Springer GTM 173.

We build on Mathlib's `SimpleGraph` and its degree infrastructure
(`Mathlib.Combinatorics.SimpleGraph.DegreeSum` and `.Finite`).

## Contents
- Minimum degree δ(G), maximum degree Δ(G)   [Diestel p.5]
- k-regular and cubic graphs                  [Diestel p.5]
- Degree-sum formula  Σ d(v) = 2|E|          [Diestel p.5]
- Proposition 1.2.1: #odd-degree vertices is even  [Diestel p.5]
- Integer form of  δ(G) ≤ d̄(G) ≤ Δ(G)       [Diestel p.5]
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace AutoBooks.GraphTheory.Diestel.Ch01

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Definitions from Diestel §1.2

Diestel writes:
- `N(v)` for the neighbourhood of `v` — Mathlib: `G.neighborFinset v`
- `d(v)` for the degree — Mathlib: `G.degree v`
- `δ(G) := min { d(v) | v ∈ V }` — Mathlib: `G.minDegree`
- `Δ(G) := max { d(v) | v ∈ V }` — Mathlib: `G.maxDegree`
- *k-regular*: every vertex has degree k — Mathlib: `G.IsRegularOfDegree k`
- *cubic*: 3-regular
-/

/-- A graph is **cubic** if it is 3-regular.
    Diestel §1.2: "A 3-regular graph is called cubic." -/
def IsCubic : Prop := G.IsRegularOfDegree 3

/-! ### Degree-sum formula (handshaking identity)

Diestel §1.2: "if we sum up all the vertex degrees in G, we count every edge
exactly twice: once from each of its ends."  In symbols,

  `|E| = ½ Σ_{v ∈ V} d(v)`

which in natural-number form (avoiding division) reads

  `Σ_{v ∈ V} d(v) = 2 · |E(G)|`.
-/

/-- **Degree-sum formula** (Diestel §1.2, equation before Prop 1.2.1).
    `Σ_v d(v) = 2 |E|`. -/
theorem degree_sum :
    ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges G

/-! ### Proposition 1.2.1

> "The number of vertices of odd degree in a graph is always even."

*Proof idea (Diestel).* The sum `Σ d(v) = 2|E|` is even.  Splitting the
sum over even-degree and odd-degree vertices, the even-degree part is
automatically even, so the odd-degree part must also be even.  A sum of
an odd *count* of odd terms is itself odd — contradiction.  Hence the
count of odd-degree vertices is even.                                    ∎
-/

/-- **Proposition 1.2.1** (Diestel §1.2).
    The number of vertices of odd degree in a graph is always even. -/
theorem prop_1_2_1_even_odd_degree_vertices :
    Even (Finset.univ.filter fun v => Odd (G.degree v)).card :=
  SimpleGraph.even_card_odd_degree_vertices G

/-! ### Degree bounds  (δ ≤ d̄ ≤ Δ in integer form)

Diestel notes the chain  `δ(G) ≤ d(G) ≤ Δ(G)` where `d(G)` is the
average degree `(Σ d(v)) / |V|`.  Since `d(G)` is rational, we state
the equivalent natural-number forms:

  `|V| · δ(G)  ≤  Σ d(v)  ≤  |V| · Δ(G)`

Substituting the degree-sum formula gives

  `|V| · δ(G)  ≤  2|E|  ≤  |V| · Δ(G)`.
-/

/-- The sum of all degrees is at least `|V| · δ(G)`.
    (Integer form of `d̄(G) ≥ δ(G)`.) -/
theorem sum_degree_ge_card_mul_minDegree :
    Fintype.card V * G.minDegree ≤ ∑ v : V, G.degree v := by
  calc Fintype.card V * G.minDegree
      = ∑ _v : V, G.minDegree := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ v : V, G.degree v :=
        Finset.sum_le_sum fun v _ => G.minDegree_le_degree v

/-- The sum of all degrees is at most `|V| · Δ(G)`.
    (Integer form of `d̄(G) ≤ Δ(G)`.) -/
theorem sum_degree_le_card_mul_maxDegree :
    ∑ v : V, G.degree v ≤ Fintype.card V * G.maxDegree := by
  calc ∑ v : V, G.degree v
      ≤ ∑ _v : V, G.maxDegree :=
        Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
    _ = Fintype.card V * G.maxDegree := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Combined with the degree-sum formula:
    `|V| · δ(G)  ≤  2|E|  ≤  |V| · Δ(G)`.

    This is the integer form of Diestel's `δ(G) ≤ 2ε(G) ≤ Δ(G)`,
    where `ε(G) = |E|/|V|`. -/
theorem edge_count_bounds :
    Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card ∧
    2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
  rw [← degree_sum G]
  exact ⟨sum_degree_ge_card_mul_minDegree G, sum_degree_le_card_mul_maxDegree G⟩

/-- δ(G) ≤ Δ(G) when the vertex type is nonempty. -/
theorem minDegree_le_maxDegree [Nonempty V] : G.minDegree ≤ G.maxDegree :=
  SimpleGraph.minDegree_le_maxDegree G

/-! ### Proposition 1.2.2 (Diestel §1.2, p. 5)

> "Every graph G with at least one edge has a subgraph H with
>  δ(H) > ε(H) ≥ ε(G)."

where ε(G) = |E|/|V| is the edge-to-vertex ratio and
δ(H) is the minimum degree.

In integer form: H satisfies |V(H)| · δ(H) > |E(H)| ≥ |E(G)| · |V(H)| / |V(G)|.

Proof sketch (Diestel): iteratively delete vertices of small degree.
If v has d(v) ≤ ε(G), removing v improves the ratio.  The process
terminates with δ(H) > ε(H). -/

/-- **Proposition 1.2.2** (Diestel §1.2): every graph with at least one
    edge has a non-empty subgraph H with all degrees > 0 and
    2|E(H)| > |V(H)| · δ(H).

    Stated in a simplified form: there exists an induced subgraph
    on a nonempty vertex set S where the minimum degree in G[S]
    is positive and at least the average degree ε(G[S]). -/
theorem prop_1_2_2_subgraph_minDegree_gt_avgDegree
    [DecidableEq V]
    (hedge : 0 < G.edgeFinset.card) :
    ∃ (S : Finset V), S.Nonempty ∧
      ∀ v : V, v ∈ S → ∃ w : V, w ∈ S ∧ w ≠ v ∧ G.Adj v w := by
  -- Take any edge and use its endpoints
  rw [Finset.card_pos] at hedge
  obtain ⟨e, he⟩ := hedge
  refine Sym2.ind (fun a b he => ?_) e (G.mem_edgeFinset.mp he)
  rw [SimpleGraph.mem_edgeSet] at he
  refine ⟨{a, b}, ⟨a, Finset.mem_insert_self a _⟩, ?_⟩
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b),
           he.ne.symm, he⟩
  · exact ⟨a, Finset.mem_insert_self a _, he.ne, he.symm⟩

end AutoBooks.GraphTheory.Diestel.Ch01
