import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointCases
import FourColor.Curriculum.Actual.SevenVertexRealization

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- Every vertex in a connected component distinct from the endpoint component has degree `2`.

Source: helper theorem for the remaining seven-vertex `15`-edge endpoint branch. The two
degree-`1` vertices already lie in the endpoint component, so every vertex in any other component
falls under the degree-`2` clause. -/
theorem forall_degree_eq_two_on_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    {d : H.ConnectedComponent} (hcd : d ≠ H.connectedComponentMk u) :
    ∀ w : W, w ∈ d.supp → H.degree w = 2 := by
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have hu_mem : u ∈ c.supp := by
    simpa [c] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := u))
  have hreach : H.Reachable u v :=
    reachable_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) huv hu1 hv1 hrest
  have hv_mem : v ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [c] using hreach.symm
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) (by simpa [c] using hcd.symm)
  intro w hw
  have hwu : w ≠ u := by
    intro hEq
    exact Set.disjoint_left.mp hdisj_cd (hEq ▸ hu_mem) hw
  have hwv : w ≠ v := by
    intro hEq
    exact Set.disjoint_left.mp hdisj_cd (hEq ▸ hv_mem) hw
  exact hrest w hwu hwv

/-- In the seven-vertex endpoint branch, the endpoint component and any distinct connected
component already exhaust all vertices.

Source: helper theorem upgrading the previous endpoint-path split to an exact two-component
realization. A third component would have size at least `3`, contradicting the seven-vertex
bound. -/
theorem endpoint_connectedComponent_union_eq_univ_of_card_eq_seven_of_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 7)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    {d : H.ConnectedComponent} (hcd : d ≠ H.connectedComponentMk u) :
    (H.connectedComponentMk u).supp ∪ d.supp = Set.univ := by
  classical
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have hu_mem : u ∈ c.supp := by
    simpa [c] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := u))
  have hreach : H.Reachable u v :=
    reachable_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) huv hu1 hv1 hrest
  have hv_mem : v ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [c] using hreach.symm
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) (by simpa [c] using hcd.symm)
  have hcge2 : 2 ≤ c.supp.ncard := by
    have hgt : 1 < c.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨u, hu_mem, v, hv_mem, huv⟩
    omega
  have hddeg : ∀ w : W, w ∈ d.supp → H.degree w = 2 :=
    forall_degree_eq_two_on_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) huv hu1 hv1 hrest hcd
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) d hddeg
  by_contra hunion
  have hunion_le : (c.supp ∪ d.supp).ncard ≤ (Set.univ : Set W).ncard := by
    exact Set.ncard_le_ncard (show c.supp ∪ d.supp ⊆ (Set.univ : Set W) by
      intro x hx
      simp)
  have hunion_lt : (c.supp ∪ d.supp).ncard < (Set.univ : Set W).ncard := by
    by_contra hnotlt
    have heq_card : (c.supp ∪ d.supp).ncard = (Set.univ : Set W).ncard :=
      Nat.le_antisymm hunion_le (Nat.not_lt.mp hnotlt)
    have heq : c.supp ∪ d.supp = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le
        (show c.supp ∪ d.supp ⊆ (Set.univ : Set W) by
          intro x hx
          simp)
      simpa [heq_card]
    exact hunion heq
  obtain ⟨w, -, hwout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hunion_lt
  let e : H.ConnectedComponent := H.connectedComponentMk w
  have hwe : w ∈ e.supp := by
    simpa [e] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := w))
  have hce : e ≠ c := by
    intro hEq
    exact hwout (Or.inl (hEq ▸ hwe))
  have hde : e ≠ d := by
    intro hEq
    exact hwout (Or.inr (hEq ▸ hwe))
  have hdisj_ce : Disjoint c.supp e.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hce.symm
  have hdisj_de : Disjoint d.supp e.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hde.symm
  have hedeg : ∀ x : W, x ∈ e.supp → H.degree x = 2 := by
    intro x hx
    have hxu : x ≠ u := by
      intro hEq
      exact Set.disjoint_left.mp hdisj_ce (hEq ▸ hu_mem) hx
    have hxv : x ≠ v := by
      intro hEq
      exact Set.disjoint_left.mp hdisj_ce (hEq ▸ hv_mem) hx
    exact hrest x hxu hxv
  have hege3 : 3 ≤ e.supp.ncard :=
    connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) e hedeg
  have hdisj_cd_e : Disjoint (c.supp ∪ d.supp) e.supp := by
    rw [Set.disjoint_union_left]
    exact ⟨hdisj_ce, hdisj_de⟩
  have htriple_le : c.supp.ncard + d.supp.ncard + e.supp.ncard ≤ 7 := by
    calc
      c.supp.ncard + d.supp.ncard + e.supp.ncard = (c.supp ∪ d.supp ∪ e.supp).ncard := by
        rw [Set.ncard_union_eq hdisj_cd_e, Set.ncard_union_eq hdisj_cd]
      _ ≤ (Set.univ : Set W).ncard := by
        exact Set.ncard_le_ncard (show c.supp ∪ d.supp ∪ e.supp ⊆ (Set.univ : Set W) by
          intro x hx
          simp)
      _ = 7 := by simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  omega

/-- In the seven-vertex endpoint branch, the endpoint component has cardinality
`7 - d.supp.ncard` for any distinct connected component `d`.

Source: helper theorem extracting the exact path-component size from the size of the leftover
cycle component. -/
theorem endpoint_connectedComponent_ncard_eq_sub_of_card_eq_seven_of_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 7)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    {d : H.ConnectedComponent} (hcd : d ≠ H.connectedComponentMk u) :
    (H.connectedComponentMk u).supp.ncard = 7 - d.supp.ncard := by
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) (by simpa [c] using hcd.symm)
  have hunion :
      c.supp ∪ d.supp = Set.univ :=
    endpoint_connectedComponent_union_eq_univ_of_card_eq_seven_of_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) hcard huv hu1 hv1 hrest hcd
  have hsum : c.supp.ncard + d.supp.ncard = 7 := by
    calc
      c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
        rw [Set.ncard_union_eq hdisj_cd]
      _ = 7 := by simpa [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  exact Nat.eq_sub_of_add_eq hsum

/-- Any connected component distinct from the endpoint component is realized by a cycle whose
vertex set is exactly that component support.

Source: helper theorem upgrading the leftover endpoint-branch component from a cardinality witness
to an explicit cycle realization. -/
theorem exists_cycle_covering_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    {d : H.ConnectedComponent} (hcd : d ≠ H.connectedComponentMk u) :
    ∃ x : W, ∃ q : H.Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp := by
  classical
  let K : SimpleGraph d.supp := H.induce d.supp
  have hKconn : K.Connected := by
    simpa [K, SimpleGraph.ConnectedComponent.toSimpleGraph] using d.connected_toSimpleGraph
  have hKreg : K.IsRegularOfDegree 2 := by
    intro x
    have hdeg_eq : K.degree x = H.degree x := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := d.supp)
          (v := x)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := d) x.property))
    exact hdeg_eq.trans
      (forall_degree_eq_two_on_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) huv hu1 hv1 hrest hcd x x.property)
  rcases exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
      (G := K) hKconn hKreg with ⟨x, p, hp, hpverts⟩
  let φ : K →g H :=
    { toFun := fun y => y.1
      map_rel' := by
        intro a b hab
        exact hab }
  refine ⟨x, p.map φ, hp.map Subtype.val_injective, ?_⟩
  ext w
  constructor
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map] at hw
    rcases List.mem_map.mp hw with ⟨y, hy, rfl⟩
    exact y.property
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map]
    refine List.mem_map.mpr ?_
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpverts]
    simp

/-- Realization upgrade for the remaining seven-vertex endpoint branch: the endpoint component is
a path, and if it does not cover all vertices then the unique remaining component is an explicit
cycle whose support exhausts the rest.

Source: new theorem turning the endpoint-branch size split into an exact path-plus-cycle
realization. -/
theorem exists_path_covering_endpoint_component_and_cycle_component_covering_all_vertices_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 7)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = (H.connectedComponentMk u).supp ∧
      ((H.connectedComponentMk u).supp = Set.univ ∨
        ∃ d : H.ConnectedComponent, d ≠ H.connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
          (H.connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : W, ∃ q : H.Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  rcases
      exists_path_covering_endpoint_component_and_component_case_split_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) hcard huv hu1 hv1 hrest with
    ⟨p, hp, hpverts, hsplit⟩
  refine ⟨p, hp, hpverts, ?_⟩
  rcases hsplit with hcov | ⟨d, hcd, hdcard⟩
  · exact Or.inl hcov
  · rcases
        exists_cycle_covering_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
          (H := H) huv hu1 hv1 hrest hcd with
      ⟨x, q, hq, hqverts⟩
    refine Or.inr ⟨d, hcd, hdcard, ?_, x, q, hq, hqverts⟩
    exact
      endpoint_connectedComponent_union_eq_univ_of_card_eq_seven_of_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) hcard huv hu1 hv1 hrest hcd

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Incidence-critical realization upgrade for the remaining seven-vertex `15`-edge endpoint
branch.

Source: new incidence-level theorem refining the last unresolved seven-vertex `15`-edge branch to
an exact path-plus-cycle realization. -/
theorem IsIncidenceCriticalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
            ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
            ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  rcases h.fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge with
    ⟨u, v, huv, hu1, hv1, hrest⟩
  rcases
      exists_path_covering_endpoint_component_and_cycle_component_covering_all_vertices_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := Gᶜ) hcard huv hu1 hv1 hrest with
    ⟨p, hp, hpverts, hsplit⟩
  exact ⟨u, v, huv, p, hp, hpverts, hsplit⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `15`-edge endpoint realization split. -/
theorem IsVertexCriticalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
            ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
            ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  exact
    IsIncidenceCriticalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `15`-edge endpoint realization split. -/
theorem IsMinimalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
            ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
            ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  exact
    IsIncidenceCriticalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the seven-vertex `15`-edge endpoint realization split under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
            ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
            ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
