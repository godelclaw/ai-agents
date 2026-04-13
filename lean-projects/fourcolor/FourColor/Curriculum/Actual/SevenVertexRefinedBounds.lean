import FourColor.Curriculum.Actual.SevenVertexDisconnectedColoring

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, a `K₅`-free incidence-critical non-4-colorable graph has at least `15`
edges.

Source: new sharpening of the previous `[14, 18]` window using the exclusion of the `|E| = 14`
case. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card := by
  have h14 : 14 ≤ G.edgeFinset.card :=
    (h.edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree).1
  have hne14 : G.edgeFinset.card ≠ 14 :=
    h.card_edgeFinset_ne_fourteen_of_card_eq_seven hcard
  have hgt14 : 14 < G.edgeFinset.card :=
    lt_of_le_of_ne h14 (by simpa [eq_comm] using hne14)
  exact Nat.succ_le_of_lt hgt14

/-- On seven vertices, a `K₅`-free incidence-critical non-4-colorable graph has edge count in the
refined interval `[15, 18]`.

Source: new theorem combining the previous upper bound with the exclusion of the `|E| = 14`
branch. -/
theorem IsIncidenceCriticalNonColorable.refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 := by
  exact ⟨h.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree hcard hfree,
    (h.edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree).2⟩

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `15`-edge lower bound. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card :=
  h.toIncidenceCritical_four.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Vertex-critical lift of the refined seven-vertex edge window `[15, 18]`. -/
theorem IsVertexCriticalNonColorable.refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 :=
  h.toIncidenceCritical_four.refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `15`-edge lower bound. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift of the refined seven-vertex edge window `[15, 18]`. -/
theorem IsMinimalNonColorable.refined_edge_bounds_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 :=
  (h.toIncidenceCritical hadj).refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalBranch

end FourColor.Curriculum.Actual
