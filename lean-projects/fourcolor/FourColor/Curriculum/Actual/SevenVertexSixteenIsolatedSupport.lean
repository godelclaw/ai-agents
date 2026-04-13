import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSixteenComplement
import FourColor.Curriculum.Actual.SevenVertexRealization

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A finite `2`-regular graph on five vertices is connected.

Source: new helper theorem for the first exact seven-vertex `16`-edge complement branch. If the
graph were disconnected, two disjoint connected components would each have at least three
vertices, contradicting the total cardinality `5`. -/
theorem connected_of_card_eq_five_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 5) (hreg : G.IsRegularOfDegree 2) :
    G.Connected := by
  classical
  by_contra hnot
  have hpos : 0 < Fintype.card V := by omega
  let v : V := Classical.choice (Fintype.card_pos_iff.mp hpos)
  let c : G.ConnectedComponent := G.connectedComponentMk v
  have hv : v ∈ c.supp := by
    simpa [c] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := v))
  have hge3c : 3 ≤ c.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg c
  have hltc : c.supp.ncard < (Set.univ : Set V).ncard := by
    have hsubset : c.supp ⊆ (Set.univ : Set V) := by
      intro x hx
      simp
    have hle : c.supp.ncard ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard hsubset
    by_contra hnotlt
    have hEqCard : c.supp.ncard = (Set.univ : Set V).ncard :=
      Nat.le_antisymm hle (Nat.not_lt.mp hnotlt)
    have hsupp : c.supp = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le hsubset
      simpa [hEqCard]
    exact hnot
      (connected_of_connectedComponent_ncard_eq_card (G := G) c
        (by simpa [hsupp, Set.ncard_univ, Nat.card_eq_fintype_card]))
  obtain ⟨w, -, hwnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hltc
  let d : G.ConnectedComponent := G.connectedComponentMk w
  have hwd : w ∈ d.supp := by
    simpa [d] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := w))
  have hcd : c ≠ d := by
    intro hEq
    exact hwnot (hEq ▸ hwd)
  have hge3d : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg d
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := G)) hcd
  have hunion_le : (c.supp ∪ d.supp).ncard ≤ (Set.univ : Set V).ncard := by
    exact Set.ncard_le_ncard (by intro x hx; simp)
  have hunion_eq : (c.supp ∪ d.supp).ncard = c.supp.ncard + d.supp.ncard := by
    rw [Set.ncard_union_eq hdisj]
  have hsum_ge6 : 6 ≤ (c.supp ∪ d.supp).ncard := by
    rw [hunion_eq]
    omega
  have htop : (c.supp ∪ d.supp).ncard ≤ 5 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using hunion_le
  omega

/-- A finite `2`-regular graph on five vertices is realized by a single cycle covering all
vertices.

Source: new helper theorem specializing the generic connected `2`-regular realization theorem to
the five-vertex support appearing in the first exact seven-vertex `16`-edge complement branch. -/
theorem exists_cycle_covering_all_vertices_of_card_eq_five_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 5) (hreg : G.IsRegularOfDegree 2) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  exact exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
    (G := G) (connected_of_card_eq_five_of_isRegularOfDegree_two hcard hreg) hreg

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the `(5,0,2)` seven-vertex `16`-edge branch, the complement support is a single `5`-cycle.

Source: new theorem combining the complement translation for the rigid `(5,0,2)` profile with the
five-vertex `2`-regular realization theorem. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_profile_five_zero_two
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  rcases h.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_profile_five_zero_two
      hcard hedge hprof with ⟨u, v, huv, hu0, hv0, hsupp, hreg⟩
  rcases exists_cycle_covering_all_vertices_of_card_eq_five_of_isRegularOfDegree_two
      (G := ((Gᶜ).induce (Gᶜ.support))) hsupp hreg with ⟨x, p, hpcycle, hpverts⟩
  exact ⟨u, v, huv, hu0, hv0, x, p, hpcycle, hpverts⟩

/-- In the live seven-vertex `K₅`-free incidence-critical branch, the isolated-pair complement
case realizes the support as a single `5`-cycle.

Source: new theorem packaging the first exact complement branch of the live seven-vertex frontier.
-/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  rcases hcase with ⟨u, v, huv, hu0, hv0, hsupp, hreg⟩
  rcases exists_cycle_covering_all_vertices_of_card_eq_five_of_isRegularOfDegree_two
      (G := ((Gᶜ).induce (Gᶜ.support))) hsupp hreg with ⟨x, p, hpcycle, hpverts⟩
  exact ⟨u, v, huv, hu0, hv0, x, p, hpcycle, hpverts⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex isolated-pair complement-cycle realization. -/
theorem IsVertexCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ :=
  (h.toIncidenceCritical_four).exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
      hcard hfree hcase

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex isolated-pair complement-cycle realization. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
          p.IsCycle ∧ p.toSubgraph.verts = Set.univ :=
  (h.toIncidenceCritical hadj).exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
      hcard hfree hcase

/-- Minimal-counterexample lift of the seven-vertex isolated-pair complement-cycle realization
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∃ (x : Gᶜ.support) (p : ((Gᶜ).induce (Gᶜ.support)).Walk x x),
        p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_distinct_two_compl_degree_eq_zero_and_compl_support_cycle_of_card_eq_seven_of_cliqueFree
      hcard hfree hcase

end MinimalBridge

end FourColor.Curriculum.Actual
