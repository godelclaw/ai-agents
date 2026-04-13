import FourColor.Curriculum.Actual.FiveVertexCycleIso
import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSixteenExactRealization

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the live seven-vertex `K₅`-free exact `|E| = 16` frontier, the surviving complement support
is exactly a transported `5`-cycle.

Source: combines the exact seven-vertex raw complement realization with the generic five-vertex
`2`-regular cycle characterization. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ e : Fin 5 ≃ Gᶜ.support,
        ((Gᶜ).induce (Gᶜ.support)) = (SimpleGraph.cycleGraph 5).map e.toEmbedding := by
  rcases h.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
      hcard hfree with ⟨u, v, huv, hu0, hv0, hsupp, hreg⟩
  rcases exists_equiv_cycleGraph_five_of_card_eq_five_of_isRegularOfDegree_two
      (G := (Gᶜ).induce (Gᶜ.support)) hsupp hreg with ⟨e, hEq⟩
  exact ⟨u, v, huv, hu0, hv0, e, hEq⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the exact seven-vertex `5`-cycle support characterization. -/
theorem IsVertexCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ e : Fin 5 ≃ Gᶜ.support,
        ((Gᶜ).induce (Gᶜ.support)) = (SimpleGraph.cycleGraph 5).map e.toEmbedding := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical_four
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
      hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the exact seven-vertex `5`-cycle support characterization. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ e : Fin 5 ≃ Gᶜ.support,
        ((Gᶜ).induce (Gᶜ.support)) = (SimpleGraph.cycleGraph 5).map e.toEmbedding := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the exact seven-vertex `5`-cycle support characterization
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ e : Fin 5 ≃ Gᶜ.support,
        ((Gᶜ).induce (Gᶜ.support)) = (SimpleGraph.cycleGraph 5).map e.toEmbedding := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
      hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
