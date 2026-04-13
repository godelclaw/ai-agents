import FourColor.Curriculum.Actual.SevenVertexSeventeenProfileThreeTwoTwo
import FourColor.Curriculum.Actual.SevenVertexSixteenInhabited

namespace FourColor.Curriculum.Actual

section IncidenceSharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact seven-vertex `|E| = 16` incidence-critical `K₅`-free frontier is sharp:
every such graph has exactly sixteen edges, and on every seven-vertex type there exists one.

Source: packages the universal exactness theorem from the seven-vertex `17`-edge exclusion together
with the transported critical witness. This is the formal repair point showing the `|E| = 16`
frontier is not an exclusion target but an inhabited endpoint. -/
theorem incidenceCritical_exact_sixteen_frontier_is_sharp_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      IsIncidenceCriticalNonColorable G 4 → G.CliqueFree 5 → G.edgeFinset.card = 16) ∧
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsIncidenceCriticalNonColorable G 4) := by
  refine ⟨?_, ?_⟩
  · intro G _ h hfree
    exact h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  · exact exists_sixteen_edge_cliqueFree_five_incidenceCritical_nonColorable_four_of_card_eq_seven
      (V := V) hcard

/-- Consequently, any blanket exclusion of the seven-vertex `|E| = 16` incidence-critical
`K₅`-free branch is false.

Source: direct corollary of the abstract transported witness. -/
theorem not_forall_card_edgeFinset_ne_sixteen_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ¬ ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      G.CliqueFree 5 → IsIncidenceCriticalNonColorable G 4 → G.edgeFinset.card ≠ 16 := by
  intro hall
  rcases
      exists_sixteen_edge_cliqueFree_five_incidenceCritical_nonColorable_four_of_card_eq_seven
        (V := V) hcard with
    ⟨G, hdec, hedge, hfree, hcrit⟩
  letI := hdec
  exact (hall (G := G) hfree hcrit) hedge

end IncidenceSharpness

section VertexSharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex-critical version of the exact seven-vertex `|E| = 16` sharpness statement.

Source: packages the vertex-critical exactness theorem with the transported vertex-critical
witness. -/
theorem vertexCritical_exact_sixteen_frontier_is_sharp_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      IsVertexCriticalNonColorable G 4 → G.CliqueFree 5 → G.edgeFinset.card = 16) ∧
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsVertexCriticalNonColorable G 4) := by
  refine ⟨?_, ?_⟩
  · intro G _ h hfree
    exact h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  · exact exists_sixteen_edge_cliqueFree_five_vertexCritical_nonColorable_four_of_card_eq_seven
      (V := V) hcard

/-- Consequently, any blanket exclusion of the seven-vertex `|E| = 16` vertex-critical
`K₅`-free branch is false.

Source: direct corollary of the transported vertex-critical witness. -/
theorem not_forall_vertexCritical_card_edgeFinset_ne_sixteen_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ¬ ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      G.CliqueFree 5 → IsVertexCriticalNonColorable G 4 → G.edgeFinset.card ≠ 16 := by
  intro hall
  rcases
      exists_sixteen_edge_cliqueFree_five_vertexCritical_nonColorable_four_of_card_eq_seven
        (V := V) hcard with
    ⟨G, hdec, hedge, hfree, hcrit⟩
  letI := hdec
  exact (hall (G := G) hfree hcrit) hedge

end VertexSharpness

end FourColor.Curriculum.Actual
