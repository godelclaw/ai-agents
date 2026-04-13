import FourColor.Curriculum.Actual.FiveVertexClassification

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has `minDegree = 4`.

Source: new theorem combining the local lower bound (`minDegree ≥ 4`) with the AES upper bound
(`minDegree ≤ 8|V|/11 = 4` when `|V| = 6`). -/
theorem IsIncidenceCriticalNonColorable.minDegree_eq_four_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.minDegree = 4 := by
  have hpos : 0 < Fintype.card V := by
    rw [hcard]
    decide
  have hne : Nonempty V := Fintype.card_pos_iff.1 hpos
  letI : Nonempty V := hne
  have hge : 4 ≤ G.minDegree := h.four_le_minDegree
  have hlow : G.minDegree ≤ 8 * Fintype.card V / 11 := by
    rcases h.k5_or_low_minDegree with hk5 | hlow
    · exact (False.elim (hk5 hfree))
    · exact hlow
  have hle : G.minDegree ≤ 4 := by
    simpa [hcard] using hlow
  exact Nat.le_antisymm hle hge

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has a degree-`4` vertex.

Source: new theorem from the exact `minDegree = 4` result and existence of a minimal-degree vertex. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_four_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 := by
  have hpos : 0 < Fintype.card V := by
    rw [hcard]
    decide
  have hne : Nonempty V := Fintype.card_pos_iff.1 hpos
  letI : Nonempty V := hne
  have hmin : G.minDegree = 4 :=
    h.minDegree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  exact ⟨v, by simpa [hmin] using hv.symm⟩

/-- On six vertices, every degree in a `K₅`-free incidence-critical non-4-colorable graph is at
most `5`.

Source: new theorem from the finite bound `degree < |V| = 6`. -/
theorem IsIncidenceCriticalNonColorable.degree_le_five_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) (v : V) :
    G.degree v ≤ 5 := by
  have _ : DecidableEq V := inferInstance
  have _ := h
  have _ := hfree
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hlt6 : G.degree v < 6 := by
    simpa [hcard] using hlt
  exact Nat.lt_succ_iff.mp hlt6

/-- On six vertices, every degree in a `K₅`-free incidence-critical non-4-colorable graph lies in
the interval `[4, 5]`.

Source: new theorem combining critical lower and finite upper degree bounds. -/
theorem IsIncidenceCriticalNonColorable.degree_window_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) (v : V) :
    4 ≤ G.degree v ∧ G.degree v ≤ 5 :=
  ⟨h.four_le_degree v, h.degree_le_five_of_card_eq_six_of_cliqueFree hcard hfree v⟩

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has `minDegree = 4`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.minDegree_eq_four_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.minDegree = 4 :=
  h.toIncidenceCritical_four.minDegree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has a degree-`4` vertex.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_degree_eq_four_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 :=
  h.toIncidenceCritical_four.exists_degree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, every degree in a `K₅`-free vertex-critical non-4-colorable graph is at most
`5`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.degree_le_five_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) (v : V) :
    G.degree v ≤ 5 :=
  h.toIncidenceCritical_four.degree_le_five_of_card_eq_six_of_cliqueFree hcard hfree v

/-- On six vertices, every degree in a `K₅`-free vertex-critical non-4-colorable graph lies in
the interval `[4, 5]`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.degree_window_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) (v : V) :
    4 ≤ G.degree v ∧ G.degree v ≤ 5 :=
  h.toIncidenceCritical_four.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
`minDegree = 4`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.minDegree_eq_four_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.minDegree = 4 :=
  (h.toIncidenceCritical hadj).minDegree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
a degree-`4` vertex.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_degree_eq_four_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 :=
  (h.toIncidenceCritical hadj).exists_degree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, every degree in a `K₅`-free edge-minimal non-4-colorable graph with no
isolated vertices lies in the interval `[4, 5]`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.degree_window_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) (v : V) :
    4 ≤ G.degree v ∧ G.degree v ≤ 5 :=
  (h.toIncidenceCritical hadj).degree_window_of_card_eq_six_of_cliqueFree hcard hfree v

end MinimalBranch

end FourColor.Curriculum.Actual
