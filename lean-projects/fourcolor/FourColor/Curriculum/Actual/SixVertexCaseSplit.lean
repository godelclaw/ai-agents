import FourColor.Curriculum.Actual.SixVertexEdgeBounds

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph falls into one of three
structural edge/degree cases:
1. `|E| = 12` and the graph is 4-regular;
2. `|E| = 13` and there are two distinct degree-`5` vertices;
3. `|E| = 14` and there exists a degree-`5` vertex.

Source: new theorem combining the edge window `[12,14]` with the corresponding branch lemmas. -/
theorem IsIncidenceCriticalNonColorable.six_vertex_edge_degree_case_split_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) ∨
    (G.edgeFinset.card = 14 ∧ ∃ v : V, G.degree v = 5) := by
  have hwin : 12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 14 :=
    h.card_edgeFinset_window_of_card_eq_six_of_cliqueFree hcard hfree
  rcases hwin with ⟨h12, h14⟩
  rcases Nat.eq_or_lt_of_le h14 with hEq14 | hLt14
  · refine Or.inr (Or.inr ?_)
    refine ⟨hEq14, ?_⟩
    exact h.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen hcard hfree hEq14
  · have h13le : G.edgeFinset.card ≤ 13 := Nat.lt_succ_iff.mp hLt14
    rcases Nat.eq_or_lt_of_le h13le with hEq13 | hLt13
    · refine Or.inr (Or.inl ?_)
      refine ⟨hEq13, ?_⟩
      exact h.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen hcard hfree hEq13
    · have h12le : G.edgeFinset.card ≤ 12 := Nat.lt_succ_iff.mp hLt13
      have hEq12 : G.edgeFinset.card = 12 := Nat.le_antisymm h12le h12
      refine Or.inl ⟨hEq12, ?_⟩
      intro v
      exact h.degree_eq_four_of_card_edgeFinset_eq_twelve hcard hfree hEq12 v

/-- Refined six-vertex `K₅`-free case split for incidence-critical non-4-colorable graphs:
`|E|=14` is eliminated by Turán's edge bound, so only two branches remain.

Source: new theorem from `six_vertex_edge_degree_case_split_of_cliqueFree` plus the bound
`|E| ≤ 13`. -/
theorem IsIncidenceCriticalNonColorable.six_vertex_edge_degree_case_split_refined_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) := by
  rcases h.six_vertex_edge_degree_case_split_of_cliqueFree hcard hfree with h12 | h13 | h14
  · exact Or.inl h12
  · exact Or.inr h13
  · rcases h14 with ⟨hEq14, _⟩
    exact (h.card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree hcard hfree hEq14).elim

/-- Exact refined six-vertex `K₅`-free case split for incidence-critical non-4-colorable graphs:
either the graph is 4-regular with `12` edges, or it has `13` edges with exactly two degree-`5`
vertices and every other vertex of degree `4`.

Source: new theorem from the refined case split plus the exact degree-pattern theorem for the
`|E| = 13` branch. -/
theorem IsIncidenceCriticalNonColorable.six_vertex_edge_degree_case_split_exact_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧
      ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
        ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4) := by
  rcases h.six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree with h12 | h13
  · exact Or.inl h12
  · rcases h13 with ⟨hEq13, huv⟩
    refine Or.inr ⟨hEq13, ?_⟩
    exact h.exists_distinct_degree_eq_five_forall_degree_eq_four_else_of_card_edgeFinset_eq_thirteen
      hcard hfree hEq13

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the six-vertex edge/degree case split. -/
theorem IsVertexCriticalNonColorable.six_vertex_edge_degree_case_split_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) ∨
    (G.edgeFinset.card = 14 ∧ ∃ v : V, G.degree v = 5) :=
  h.toIncidenceCritical_four.six_vertex_edge_degree_case_split_of_cliqueFree hcard hfree

/-- Vertex-critical lift of the refined six-vertex `K₅`-free case split. -/
theorem IsVertexCriticalNonColorable.six_vertex_edge_degree_case_split_refined_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) :=
  h.toIncidenceCritical_four.six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Edge-minimal + no-isolated lift of the six-vertex edge/degree case split. -/
theorem IsMinimalNonColorable.six_vertex_edge_degree_case_split_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) ∨
    (G.edgeFinset.card = 14 ∧ ∃ v : V, G.degree v = 5) :=
  (h.toIncidenceCritical hadj).six_vertex_edge_degree_case_split_of_cliqueFree hcard hfree

/-- Edge-minimal + no-isolated lift of the refined six-vertex `K₅`-free case split. -/
theorem IsMinimalNonColorable.six_vertex_edge_degree_case_split_refined_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ ∀ v : V, G.degree v = 4) ∨
    (G.edgeFinset.card = 13 ∧ ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5) :=
  (h.toIncidenceCritical hadj).six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree

end MinimalBranch

end FourColor.Curriculum.Actual
