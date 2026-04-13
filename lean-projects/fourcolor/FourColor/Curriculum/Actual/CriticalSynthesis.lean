import FourColor.Curriculum.Actual.VertexCritical

namespace FourColor.Curriculum.Actual

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- For edge-minimal non-4-colorable graphs with no isolated vertices, we recover the same
`K₅`/min-degree window as incidence-critical graphs via the bridge theorem.

Source: new synthesis theorem. -/
theorem IsMinimalNonColorable.k5_or_minDegree_window_of_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    ¬ G.CliqueFree 5 ∨
      (4 ≤ G.minDegree ∧ G.minDegree ≤ 8 * Fintype.card V / 11) :=
  (h.toIncidenceCritical hadj).k5_or_minDegree_window

/-- For edge-minimal non-4-colorable graphs with no isolated vertices, there are at least five
vertices.

Source: new synthesis theorem. -/
theorem IsMinimalNonColorable.card_verts_ge_five_of_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    5 ≤ Fintype.card V :=
  (h.toIncidenceCritical hadj).card_verts_ge_five

/-- For edge-minimal non-4-colorable graphs with no isolated vertices, `K₅`-freeness implies
at least six vertices.

Source: new synthesis theorem. -/
theorem IsMinimalNonColorable.card_verts_ge_six_of_cliqueFree_and_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hfree : G.CliqueFree 5) :
    6 ≤ Fintype.card V :=
  (h.toIncidenceCritical hadj).card_verts_ge_six_of_cliqueFree hfree

/-- On five vertices, an edge-minimal non-4-colorable graph with no isolated vertices cannot be
`K₅`-free.

Source: new synthesis theorem. -/
theorem IsMinimalNonColorable.not_cliqueFree_five_of_card_eq_five_and_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 5) :
    ¬ G.CliqueFree 5 := by
  intro hfree
  have h6 : 6 ≤ Fintype.card V :=
    h.card_verts_ge_six_of_cliqueFree_and_forall_exists_adj hadj hfree
  have h65 : 6 ≤ 5 := by
    have h6' : 6 ≤ Fintype.card V := h6
    rwa [hcard] at h6'
  exact (Nat.not_succ_le_self 5) h65

/-- On five vertices, an edge-minimal non-4-colorable graph with no isolated vertices contains a
`K₅` embedding.

Source: new synthesis theorem. -/
theorem IsMinimalNonColorable.exists_k5_embedding_of_card_eq_five_and_forall_exists_adj
    [Nonempty V]
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 5) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) := by
  have hnotfree : ¬ G.CliqueFree 5 :=
    h.not_cliqueFree_five_of_card_eq_five_and_forall_exists_adj hadj hcard
  exact (SimpleGraph.not_cliqueFree_iff (G := G) 5).1 hnotfree

end MinimalBridge

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]

/-- On five vertices, a vertex-critical non-4-colorable graph cannot be `K₅`-free.

Source: new synthesis theorem. -/
theorem IsVertexCriticalNonColorable.not_cliqueFree_five_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    ¬ G.CliqueFree 5 := by
  intro hfree
  have h6 : 6 ≤ Fintype.card V := h.card_verts_ge_six_of_cliqueFree hfree
  have h65 : 6 ≤ 5 := by
    have h6' : 6 ≤ Fintype.card V := h6
    rwa [hcard] at h6'
  exact (Nat.not_succ_le_self 5) h65

/-- On five vertices, a vertex-critical non-4-colorable graph contains a `K₅` embedding.

Source: new synthesis theorem. -/
theorem IsVertexCriticalNonColorable.exists_k5_embedding_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) := by
  have hnotfree : ¬ G.CliqueFree 5 := h.not_cliqueFree_five_of_card_eq_five hcard
  exact (SimpleGraph.not_cliqueFree_iff (G := G) 5).1 hnotfree

end VertexBridge

end FourColor.Curriculum.Actual
