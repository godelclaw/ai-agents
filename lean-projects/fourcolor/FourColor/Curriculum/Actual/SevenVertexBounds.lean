import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import FourColor.Curriculum.Actual.SixVertexExclusion

namespace FourColor.Curriculum.Actual

section GenericTuran

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

/-- On seven vertices, a `K₅`-free graph has at most `18` edges.

Source: Turán's theorem specialized to the `K₅`-free, seven-vertex case. -/
theorem card_edgeFinset_le_eighteen_of_card_eq_seven_of_cliqueFree
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 18 := by
  simpa [hcard] using
    (SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 4) hfree)

end GenericTuran

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Under `K₅`-freeness, a nonempty incidence-critical non-4-colorable finite graph has at least
seven vertices.

Source: new sharpening from the six-vertex exclusion theorem. -/
theorem IsIncidenceCriticalNonColorable.card_verts_ge_seven_of_cliqueFree
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4) (hfree : G.CliqueFree 5) :
    7 ≤ Fintype.card V := by
  have hge6 : 6 ≤ Fintype.card V := h.card_verts_ge_six_of_cliqueFree hfree
  have hne6 : Fintype.card V ≠ 6 := by
    intro hcard6
    exact (h.not_cliqueFree_six_of_card_eq_six hcard6) hfree
  have hgt6 : 6 < Fintype.card V := lt_of_le_of_ne hge6 (by simpa [eq_comm] using hne6)
  exact Nat.succ_le_of_lt hgt6

/-- Embedding-level version of the previous finite-size sharpening. -/
theorem IsIncidenceCriticalNonColorable.card_verts_ge_seven_of_no_k5_embedding
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4)
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G)) :
    7 ≤ Fintype.card V := by
  have hfree : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff (G := G) (n := 5)).2 hK5
  exact h.card_verts_ge_seven_of_cliqueFree hfree

/-- On seven vertices, a `K₅`-free incidence-critical non-4-colorable graph has edge count in the
interval `[14, 18]`.

Source: new theorem combining the critical lower edge bound with Turán's theorem. -/
theorem IsIncidenceCriticalNonColorable.edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    14 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 := by
  constructor
  · simpa [hcard] using h.two_mul_card_le_card_edgeFinset
  · exact card_edgeFinset_le_eighteen_of_card_eq_seven_of_cliqueFree (G := G) hcard hfree

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Under `K₅`-freeness, a nonempty vertex-critical non-4-colorable finite graph has at least
seven vertices.

Source: new sharpening via the incidence-critical bridge and the six-vertex exclusion theorem. -/
theorem IsVertexCriticalNonColorable.card_verts_ge_seven_of_cliqueFree
    [Nonempty V] (h : IsVertexCriticalNonColorable G 4) (hfree : G.CliqueFree 5) :
    7 ≤ Fintype.card V :=
  h.toIncidenceCritical_four.card_verts_ge_seven_of_cliqueFree hfree

/-- Embedding-level version of the previous finite-size sharpening. -/
theorem IsVertexCriticalNonColorable.card_verts_ge_seven_of_no_k5_embedding
    [Nonempty V] (h : IsVertexCriticalNonColorable G 4)
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G)) :
    7 ≤ Fintype.card V :=
  h.toIncidenceCritical_four.card_verts_ge_seven_of_no_k5_embedding hK5

/-- On seven vertices, a `K₅`-free vertex-critical non-4-colorable graph has edge count in the
interval `[14, 18]`.

Source: new theorem via the incidence-critical bridge. -/
theorem IsVertexCriticalNonColorable.edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    14 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 :=
  h.toIncidenceCritical_four.edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Under `K₅`-freeness, an edge-minimal non-4-colorable graph with no isolated vertices has at
least seven vertices.

Source: new sharpening via the minimal-to-incidence bridge and the six-vertex exclusion theorem. -/
theorem IsMinimalNonColorable.card_verts_ge_seven_of_cliqueFree_and_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hfree : G.CliqueFree 5) :
    7 ≤ Fintype.card V :=
  (h.toIncidenceCritical hadj).card_verts_ge_seven_of_cliqueFree hfree

/-- On seven vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices
has edge count in the interval `[14, 18]`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.edge_bounds_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    14 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 :=
  (h.toIncidenceCritical hadj).edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalBranch

end FourColor.Curriculum.Actual
