import Mathlib.Data.Set.Card
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointPaths
import FourColor.Curriculum.Actual.SevenVertexFifteenIsolatedColoring

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- A connected component in which every vertex has degree `2` has at least three vertices.

Source: helper theorem for the remaining seven-vertex `15`-edge complement branch, used to bound
the size of any cycle component outside the endpoint path component. -/
theorem connectedComponent_ncard_ge_three_of_forall_degree_eq_two
    (c : H.ConnectedComponent) (hdeg : ∀ w : W, w ∈ c.supp → H.degree w = 2) :
    3 ≤ c.supp.ncard := by
  classical
  let v : W := c.nonempty_supp.some
  have hv : v ∈ c.supp := c.nonempty_supp.some_mem
  have htwo : (H.neighborSet v).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree, hdeg v hv]
  obtain ⟨w₁, w₂, hw12, hset⟩ := Set.ncard_eq_two.mp htwo
  have hw₁mem : w₁ ∈ H.neighborSet v := by rw [hset]; simp
  have hw₂mem : w₂ ∈ H.neighborSet v := by rw [hset]; simp
  have hw₁adj : H.Adj v w₁ := by simpa [SimpleGraph.mem_neighborSet] using hw₁mem
  have hw₂adj : H.Adj v w₂ := by simpa [SimpleGraph.mem_neighborSet] using hw₂mem
  have hw₁ : w₁ ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hw₁adj
  have hw₂ : w₂ ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hw₂adj
  have hvw₁ : v ≠ w₁ := H.ne_of_adj hw₁adj
  have hvw₂ : v ≠ w₂ := H.ne_of_adj hw₂adj
  have hgt : 2 < c.supp.ncard := by
    exact (Set.two_lt_ncard).2 ⟨v, hv, w₁, hw₁, w₂, hw₂, hvw₁, hvw₂, hw12⟩
  exact Nat.succ_le_of_lt hgt

/-- In a finite graph with degree pattern `1,1,2,...,2`, the connected component containing the
two degree-`1` vertices is exactly a spanning path on that component support.

Source: new helper theorem isolating the path component for the remaining seven-vertex `15`-edge
complement branch. -/
theorem exists_path_covering_endpoint_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = (H.connectedComponentMk u).supp := by
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
  let K : SimpleGraph c.supp := H.induce c.supp
  have hKconn : K.Connected := by
    simpa [K, SimpleGraph.ConnectedComponent.toSimpleGraph] using c.connected_toSimpleGraph
  have huK1 : K.degree ⟨u, hu_mem⟩ = 1 := by
    have hdeg_eq : K.degree ⟨u, hu_mem⟩ = H.degree u := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
          (v := ⟨u, hu_mem⟩)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) hu_mem))
    exact hdeg_eq.trans hu1
  have hvK1 : K.degree ⟨v, hv_mem⟩ = 1 := by
    have hdeg_eq : K.degree ⟨v, hv_mem⟩ = H.degree v := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
          (v := ⟨v, hv_mem⟩)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) hv_mem))
    exact hdeg_eq.trans hv1
  have hrestK :
      ∀ w : c.supp, w ≠ ⟨u, hu_mem⟩ → w ≠ ⟨v, hv_mem⟩ → K.degree w = 2 := by
    intro w hwu hwv
    have hdeg_eq : K.degree w = H.degree w := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
          (v := w)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) w.property))
    exact hdeg_eq.trans (hrest w (fun h => hwu (Subtype.ext h)) (fun h => hwv (Subtype.ext h)))
  rcases exists_path_covering_all_vertices_of_connected_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := K) hKconn
      (by exact fun h => huv (Subtype.ext_iff.mp h))
      huK1 hvK1 hrestK with
    ⟨p, hp, hpverts⟩
  let φ : K →g H :=
    { toFun := fun x => x.1
      map_rel' := by
        intro a b hab
        exact hab }
  refine ⟨p.map φ, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp
  · ext w
    constructor
    · intro hw
      rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map] at hw
      rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
      exact x.property
    · intro hw
      rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map]
      refine List.mem_map.mpr ?_
      refine ⟨⟨w, hw⟩, ?_, ?_⟩
      · rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpverts]
        simp
      · rfl

/-- On seven vertices, the remaining degree pattern `1,1,2,...,2` has at most one further
connected component, and if that component exists its size is `3`, `4`, or `5`.

Source: new helper theorem reducing the non-connected seven-vertex endpoint branch to a finite
component-size split before explicit coloring. -/
theorem exists_distinct_component_card_three_four_or_five_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 7)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    (hnot : (H.connectedComponentMk u).supp ≠ Set.univ) :
    ∃ d : H.ConnectedComponent, d ≠ H.connectedComponentMk u ∧
      (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) := by
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
  have hlt : c.supp.ncard < (Set.univ : Set W).ncard := by
    by_contra hnotlt
    have hEq : c.supp = (Set.univ : Set W) := by
      apply Set.eq_of_subset_of_ncard_le (show c.supp ⊆ (Set.univ : Set W) by intro x hx; simp)
      exact Nat.not_lt.mp hnotlt
    exact hnot hEq
  obtain ⟨w, -, hw_not_mem⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  let d : H.ConnectedComponent := H.connectedComponentMk w
  have hw_mem : w ∈ d.supp := by
    simpa [d] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := w))
  have hcd : d ≠ c := by
    intro hdc
    exact hw_not_mem (hdc ▸ hw_mem)
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hcd.symm
  have hddeg : ∀ x : W, x ∈ d.supp → H.degree x = 2 := by
    intro x hx
    have hxu : x ≠ u := by
      intro hEq
      exact Set.disjoint_left.mp hdisj (hEq ▸ hu_mem) hx
    have hxv : x ≠ v := by
      intro hEq
      exact Set.disjoint_left.mp hdisj (hEq ▸ hv_mem) hx
    exact hrest x hxu hxv
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) d hddeg
  have hcge2 : 2 ≤ c.supp.ncard := by
    have hgt : 1 < c.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨u, hu_mem, v, hv_mem, huv⟩
    omega
  have hdsubset : d.supp ⊆ (Set.univ : Set W) \ c.supp := by
    intro x hx
    refine ⟨by simp, ?_⟩
    intro hxc
    exact Set.disjoint_left.mp hdisj hxc hx
  have hdle5 : d.supp.ncard ≤ 5 := by
    calc
      d.supp.ncard ≤ ((Set.univ : Set W) \ c.supp).ncard := Set.ncard_le_ncard hdsubset
      _ = 7 - c.supp.ncard := by
        rw [Set.ncard_diff (show c.supp ⊆ (Set.univ : Set W) by intro x hx; simp)]
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      _ ≤ 5 := by omega
  have hcases : d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5 := by
    omega
  exact ⟨d, by simpa [c] using hcd, hcases⟩

/-- Seven-vertex case split for the remaining degree pattern `1,1,2,...,2`: the endpoint
component is a spanning path, and either it already covers all vertices or there is one more
component of size `3`, `4`, or `5`.

Source: new finite case split theorem preparing the last unresolved seven-vertex `15`-edge
endpoint branch for explicit coloring. -/
theorem exists_path_covering_endpoint_component_and_component_case_split_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 7)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = (H.connectedComponentMk u).supp ∧
      ((H.connectedComponentMk u).supp = Set.univ ∨
        ∃ d : H.ConnectedComponent, d ≠ H.connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5)) := by
  rcases
      exists_path_covering_endpoint_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) huv hu1 hv1 hrest with
    ⟨p, hp, hpverts⟩
  refine ⟨p, hp, hpverts, ?_⟩
  by_cases hcov : (H.connectedComponentMk u).supp = Set.univ
  · exact Or.inl hcov
  · exact Or.inr
      (exists_distinct_component_card_three_four_or_five_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) hcard huv hu1 hv1 hrest hcov)

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the remaining seven-vertex `15`-edge endpoint branch, the complement has a spanning path on
the endpoint component, and the leftover geometry is either empty or a single component of size
`3`, `4`, or `5`.

Source: new incidence-level finite case split for the last unresolved seven-vertex `15`-edge
branch. -/
theorem IsIncidenceCriticalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5)) := by
  rcases h.fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge with
    ⟨u, v, huv, hu1, hv1, hrest⟩
  rcases
      exists_path_covering_endpoint_component_and_component_case_split_of_card_eq_seven_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := Gᶜ) hcard huv hu1 hv1 hrest with
    ⟨p, hp, hpverts, hsplit⟩
  exact ⟨u, v, huv, p, hp, hpverts, hsplit⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `15`-edge endpoint-path case split. -/
theorem IsVertexCriticalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5)) :=
  by
    exact
      IsIncidenceCriticalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
        (G := G) (h := h.toIncidenceCritical_four) hcard hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `15`-edge endpoint-path case split. -/
theorem IsMinimalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5)) :=
  by
    exact
      IsIncidenceCriticalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
        (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the seven-vertex `15`-edge endpoint-path case split under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        (((Gᶜ).connectedComponentMk u).supp = Set.univ ∨
          ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
            (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5)) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_endpoint_path_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
