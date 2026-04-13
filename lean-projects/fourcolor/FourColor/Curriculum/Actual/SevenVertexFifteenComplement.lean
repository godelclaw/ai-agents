import FourColor.Curriculum.Actual.SevenVertexFifteenStructure

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A degree-`6` vertex with all other degrees `4` yields an isolated complement vertex and a
`2`-regular complement support on six vertices.

Source: new helper theorem translating the first exact seven-vertex `15`-edge degree pattern into
complement degree data and then restricting to the complement support. -/
theorem compl_degree_eq_zero_card_support_eq_six_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_degree_eq_six_and_forall_degree_eq_four_else
    (hcard : Fintype.card V = 7) {u : V}
    (hu6 : G.degree u = 6) (hrest : ∀ w : V, w ≠ u → G.degree w = 4) :
    Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  have hu0 : Gᶜ.degree u = 0 := by
    simpa [hcard, hu6] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hcomp_rest : ∀ w : V, w ≠ u → Gᶜ.degree w = 2 := by
    intro w hwu
    simpa [hcard, hrest w hwu] using (SimpleGraph.degree_compl (G := G) (v := w))
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hsupp : Gᶜ.support = ({u} : Set V)ᶜ := by
    ext w
    constructor
    · intro hw
      have hwu : w ≠ u := by
        intro hEq
        exact hu_not_mem (hEq ▸ hw)
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hwu
    · intro hw
      have hwu : w ≠ u := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hw
      exact (Gᶜ.degree_pos_iff_mem_support w).1 (by simp [hcomp_rest w hwu])
  have hcard_support : Fintype.card Gᶜ.support = 6 := by
    have hcard_support_eq :
        Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u} : Set V) := by
      simpa [hsupp] using (Fintype.card_compl_set ({u} : Set V))
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u} : Set V) := hcard_support_eq
      _ = 7 - 1 := by rw [hcard]; simp
      _ = 6 := by decide
  have hreg : ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
    intro w
    rw [SimpleGraph.degree_induce_support]
    have hwu : (w : V) ≠ u := by
      intro hEq
      exact hu_not_mem (hEq ▸ w.property)
    exact hcomp_rest w hwu
  exact ⟨hu0, hcard_support, hreg⟩

/-- Two distinct degree-`5` vertices with all other degrees `4` yield exactly two complement
vertices of degree `1` and every other complement vertex has degree `2`.

Source: new helper theorem translating the second exact seven-vertex `15`-edge degree pattern into
complement degree data. -/
theorem exists_distinct_compl_degree_eq_one_forall_compl_degree_eq_two_of_card_eq_seven_of_distinct_degree_eq_five_and_forall_degree_eq_four_else
    (hcard : Fintype.card V = 7)
    {u v : V} (huv : u ≠ v) (hu5 : G.degree u = 5) (hv5 : G.degree v = 5)
    (hrest : ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 := by
  refine ⟨u, v, huv, ?_, ?_, ?_⟩
  · simpa [hcard, hu5] using (SimpleGraph.degree_compl (G := G) (v := u))
  · simpa [hcard, hv5] using (SimpleGraph.degree_compl (G := G) (v := v))
  · intro w hwu hwv
    simpa [hcard, hrest w hwu hwv] using (SimpleGraph.degree_compl (G := G) (v := w))

/-- Refined complement case split for the seven-vertex `15`-edge branch.

Source: new theorem packaging the exact complement geometry of the live seven-vertex low-edge
branch after the exclusion of `|E| = 14`. -/
theorem IsIncidenceCriticalNonColorable.fifteen_edge_compl_case_split_of_card_eq_seven
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 := by
  rcases h.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen hcard hedge with h6 | h5
  · left
    rcases h6 with ⟨u, hu6, hrest⟩
    exact ⟨u,
      (compl_degree_eq_zero_card_support_eq_six_and_induce_support_isRegularOfDegree_two_of_card_eq_seven_of_degree_eq_six_and_forall_degree_eq_four_else
        (G := G) hcard hu6 hrest)⟩
  · right
    rcases h5 with ⟨u, v, huv, hu5, hv5, hrest⟩
    exact exists_distinct_compl_degree_eq_one_forall_compl_degree_eq_two_of_card_eq_seven_of_distinct_degree_eq_five_and_forall_degree_eq_four_else
      (G := G) hcard huv hu5 hv5 hrest

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the refined seven-vertex `15`-edge complement case split. -/
theorem IsVertexCriticalNonColorable.fifteen_edge_compl_case_split_of_card_eq_seven
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 :=
  h.toIncidenceCritical_four.fifteen_edge_compl_case_split_of_card_eq_seven hcard hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the refined seven-vertex `15`-edge complement case split. -/
theorem IsMinimalNonColorable.fifteen_edge_compl_case_split_of_card_eq_seven_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 :=
  (h.toIncidenceCritical hadj).fifteen_edge_compl_case_split_of_card_eq_seven hcard hedge

/-- Minimal-counterexample lift of the refined seven-vertex `15`-edge complement case split under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.fifteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.fifteen_edge_compl_case_split_of_card_eq_seven hcard hedge

end MinimalBranch

end FourColor.Curriculum.Actual
