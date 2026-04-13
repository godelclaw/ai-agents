import FourColor.Curriculum.Actual.SevenVertexSixteenIsolatedSupport
import FourColor.Curriculum.Actual.SevenVertexSixteenProfileThreeFourZeroColoring

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the live seven-vertex `K₅`-free frontier, the exact `|E| = 16` degree-profile reduction to
`(5,0,2)` forces the raw isolated-pair complement realization.

Source: bridge theorem combining the exact degree-profile closure of the colorable
`(3,4,0)` and `(4,2,1)` branches with the rigid complement translation of `(5,0,2)`. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  have hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 5 ∧ d5 = 0 ∧ d6 = 2 :=
    h.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    h.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_profile_five_zero_two
      hcard hedge hprof

/-- In the live seven-vertex `K₅`-free frontier, the surviving exact `|E| = 16` branch forces the
complement support to be a single `5`-cycle together with two isolated complement vertices.

Source: immediate refinement of the exact raw complement realization via the five-vertex
`2`-regular cycle theorem. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  have hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 :=
    h.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
      hcard hfree
  exact
    h.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
      hcard hfree hcase

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the exact seven-vertex `|E| = 16` raw isolated-pair complement
realization. -/
theorem IsVertexCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical_four
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Vertex-critical lift of the exact seven-vertex `|E| = 16` complement-cycle realization. -/
theorem IsVertexCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical_four
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
      hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the exact seven-vertex `|E| = 16` raw isolated-pair complement
realization. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the exact seven-vertex `|E| = 16` complement-cycle
realization. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the exact seven-vertex `|E| = 16` raw isolated-pair complement
realization without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the exact seven-vertex `|E| = 16` complement-cycle realization
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_forced_of_card_eq_seven_of_cliqueFree
      hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
