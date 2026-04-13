import FourColor.Curriculum.Actual.SevenVertexMinimalEdgeBounds
import FourColor.Curriculum.Actual.SevenVertexSixteenMinimalWitness

namespace FourColor.Curriculum.Actual

section MinimalSharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact seven-vertex `|E| = 16` minimal non-`4`-colorable `K₅`-free frontier is sharp:
every such graph has exactly sixteen edges, and on every seven-vertex type there exists one.

Source: packages the support-reduced universal exactness theorem with the transported minimal
witness. -/
theorem minimal_exact_sixteen_frontier_is_sharp_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      IsMinimalNonColorable G 4 → G.CliqueFree 5 →
        G.edgeFinset.card = 16) ∧
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsMinimalNonColorable G 4) := by
  refine ⟨?_, ?_⟩
  · intro G _ h hfree
    exact h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  · exact
      exists_sixteen_edge_cliqueFree_five_minimal_nonColorable_four_of_card_eq_seven
        (V := V) hcard

/-- Consequently, any blanket exclusion of the seven-vertex `|E| = 16` minimal `K₅`-free branch
is false. -/
theorem not_forall_minimal_card_edgeFinset_ne_sixteen_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ¬ ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      G.CliqueFree 5 → IsMinimalNonColorable G 4 →
        G.edgeFinset.card ≠ 16 := by
  intro hall
  rcases
      exists_sixteen_edge_cliqueFree_five_minimal_nonColorable_four_of_card_eq_seven
        (V := V) hcard with
    ⟨G, hdec, hedge, hfree, hmin⟩
  letI := hdec
  exact (hall (G := G) hfree hmin) hedge

end MinimalSharpness

end FourColor.Curriculum.Actual
