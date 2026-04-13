import FourColor.Curriculum.Actual.SixVertexEndpointCases
import FourColor.Curriculum.Actual.SevenVertexMinimalEdgeBounds
import FourColor.Curriculum.Actual.SevenVertexSixteenComplement

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The seven-vertex `|E| = 16` degree-count profile `(4,2,1)` specializes to one isolated
complement vertex together with a six-vertex support graph of type `P₆`, `P₃ ⊔ C₃`, or
`P₂ ⊔ C₄`.

Source: new structure theorem combining the exact complement degree profile with the reusable
six-vertex endpoint-support classification. -/
theorem IsIncidenceCriticalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    ∃ z : V, Gᶜ.degree z = 0 ∧
      ∃ u v : Gᶜ.support, (u : V) ≠ v ∧
        ((Gᶜ).induce (Gᶜ.support)).degree u = 1 ∧
        ((Gᶜ).induce (Gᶜ.support)).degree v = 1 ∧
        (∀ x : Gᶜ.support, x ≠ u → x ≠ v → ((Gᶜ).induce (Gᶜ.support)).degree x = 2) ∧
        ∃ p : ((Gᶜ).induce (Gᶜ.support)).Walk u v,
          p.IsPath ∧ p.toSubgraph.verts =
            (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∧
          ((((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp = Set.univ ∨
            ∃ d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
              d ≠ ((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u ∧
              (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
              (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
              ∃ x : Gᶜ.support,
                ∃ q : ((Gᶜ).induce (Gᶜ.support)).Walk x x,
                  q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  classical
  rcases
      h.exists_distinct_compl_degree_zero_one_one_card_support_eq_six_forall_rest_degree_two_of_profile_four_two_one
        hcard hedge hprof with
    ⟨z, u, v, hzu, hzv, huv, hz0, hu1, hv1, hsupp, hrest⟩
  have hu_mem : u ∈ Gᶜ.support := by
    exact (Gᶜ.degree_pos_iff_mem_support u).1 (by simp [hu1])
  have hv_mem : v ∈ Gᶜ.support := by
    exact (Gᶜ.degree_pos_iff_mem_support v).1 (by simp [hv1])
  let uS : Gᶜ.support := ⟨u, hu_mem⟩
  let vS : Gᶜ.support := ⟨v, hv_mem⟩
  have huvS : uS ≠ vS := by
    intro hEq
    exact huv (Subtype.ext_iff.mp hEq)
  have huS1 : ((Gᶜ).induce (Gᶜ.support)).degree uS = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hu1
  have hvS1 : ((Gᶜ).induce (Gᶜ.support)).degree vS = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hv1
  have hrestS :
      ∀ x : Gᶜ.support, x ≠ uS → x ≠ vS → ((Gᶜ).induce (Gᶜ.support)).degree x = 2 := by
    intro x hxu hxv
    rw [SimpleGraph.degree_induce_support]
    exact hrest x
      (by
        intro hxz
        exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z)).mp hz0
          (hxz ▸ x.property))
      (fun hEq => hxu (Subtype.ext hEq))
      (fun hEq => hxv (Subtype.ext hEq))
  rcases
      exists_path_covering_endpoint_component_and_cycle_component_case_split_of_card_eq_six_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := ((Gᶜ).induce (Gᶜ.support))) hsupp huvS huS1 hvS1 hrestS with
    ⟨p, hp, hpverts, hsplit⟩
  exact ⟨z, hz0, uS, vS, huv, huS1, hvS1, hrestS, p, hp, hpverts, hsplit⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `16`-edge `(4,2,1)` support-path/cycle split. -/
theorem IsVertexCriticalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    ∃ z : V, Gᶜ.degree z = 0 ∧
      ∃ u v : Gᶜ.support, (u : V) ≠ v ∧
        ((Gᶜ).induce (Gᶜ.support)).degree u = 1 ∧
        ((Gᶜ).induce (Gᶜ.support)).degree v = 1 ∧
        (∀ x : Gᶜ.support, x ≠ u → x ≠ v → ((Gᶜ).induce (Gᶜ.support)).degree x = 2) ∧
        ∃ p : ((Gᶜ).induce (Gᶜ.support)).Walk u v,
          p.IsPath ∧ p.toSubgraph.verts =
            (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∧
          ((((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp = Set.univ ∨
            ∃ d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
              d ≠ ((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u ∧
              (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
              (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
              ∃ x : Gᶜ.support,
                ∃ q : ((Gᶜ).induce (Gᶜ.support)).Walk x x,
                  q.IsCycle ∧ q.toSubgraph.verts = d.supp) :=
by
  exact
    IsIncidenceCriticalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge hprof

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `16`-edge `(4,2,1)` support-path/cycle split. -/
theorem IsMinimalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    ∃ z : V, Gᶜ.degree z = 0 ∧
      ∃ u v : Gᶜ.support, (u : V) ≠ v ∧
        ((Gᶜ).induce (Gᶜ.support)).degree u = 1 ∧
        ((Gᶜ).induce (Gᶜ.support)).degree v = 1 ∧
        (∀ x : Gᶜ.support, x ≠ u → x ≠ v → ((Gᶜ).induce (Gᶜ.support)).degree x = 2) ∧
        ∃ p : ((Gᶜ).induce (Gᶜ.support)).Walk u v,
          p.IsPath ∧ p.toSubgraph.verts =
            (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∧
          ((((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp = Set.univ ∨
            ∃ d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
              d ≠ ((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u ∧
              (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
              (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
              ∃ x : Gᶜ.support,
                ∃ q : ((Gᶜ).induce (Gᶜ.support)).Walk x x,
                  q.IsCycle ∧ q.toSubgraph.verts = d.supp) :=
by
  exact
    IsIncidenceCriticalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free `(4,2,1)` support-path/cycle
split without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    ∃ z : V, Gᶜ.degree z = 0 ∧
      ∃ u v : Gᶜ.support, (u : V) ≠ v ∧
        ((Gᶜ).induce (Gᶜ.support)).degree u = 1 ∧
        ((Gᶜ).induce (Gᶜ.support)).degree v = 1 ∧
        (∀ x : Gᶜ.support, x ≠ u → x ≠ v → ((Gᶜ).induce (Gᶜ.support)).degree x = 2) ∧
        ∃ p : ((Gᶜ).induce (Gᶜ.support)).Walk u v,
          p.IsPath ∧ p.toSubgraph.verts =
            (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∧
          ((((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp = Set.univ ∨
            ∃ d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
              d ≠ ((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u ∧
              (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
              (((Gᶜ).induce (Gᶜ.support)).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
              ∃ x : Gᶜ.support,
                ∃ q : ((Gᶜ).induce (Gᶜ.support)).Walk x x,
                  q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

end MinimalBridge

end FourColor.Curriculum.Actual
