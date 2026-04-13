import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointRealization

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- On six vertices, the degree pattern `1,1,2,...,2` has at most one further connected
component, and if that component exists then its cardinality is `3` or `4`.

Source: new helper theorem for the seven-vertex `|E| = 16` profile `(4,2,1)`, obtained by
running the endpoint-component argument on the six-vertex complement support. -/
theorem exists_distinct_component_card_three_or_four_of_card_eq_six_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 6)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2)
    (hnot : (H.connectedComponentMk u).supp ≠ Set.univ) :
    ∃ d : H.ConnectedComponent, d ≠ H.connectedComponentMk u ∧
      (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
      (H.connectedComponentMk u).supp ∪ d.supp = Set.univ := by
  classical
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have hu_mem : u ∈ c.supp := by
    simpa [c] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := u))
  have hreach : H.Reachable u v :=
    reachable_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) huv hu1 hv1 hrest
  have hv_mem : v ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [c] using hreach.symm
  have hlt : c.supp.ncard < (Set.univ : Set W).ncard := by
    by_contra hnotlt
    have hEq : c.supp = (Set.univ : Set W) := by
      apply Set.eq_of_subset_of_ncard_le (show c.supp ⊆ (Set.univ : Set W) by
        intro x hx
        simp)
      exact Nat.not_lt.mp hnotlt
    exact hnot hEq
  obtain ⟨w, -, hw_not_mem⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  let d : H.ConnectedComponent := H.connectedComponentMk w
  have hw_mem : w ∈ d.supp := by
    simpa [d] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := w))
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
  have hcge2 : 2 ≤ c.supp.ncard := by
    have hgt : 1 < c.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨u, hu_mem, v, hv_mem, huv⟩
    omega
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) d hddeg
  have hdsubset : d.supp ⊆ (Set.univ : Set W) \ c.supp := by
    intro x hx
    refine ⟨by simp, ?_⟩
    intro hxc
    exact Set.disjoint_left.mp hdisj hxc hx
  have hdle4 : d.supp.ncard ≤ 4 := by
    calc
      d.supp.ncard ≤ ((Set.univ : Set W) \ c.supp).ncard := Set.ncard_le_ncard hdsubset
      _ = 6 - c.supp.ncard := by
        rw [Set.ncard_diff (show c.supp ⊆ (Set.univ : Set W) by
          intro x hx
          simp)]
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      _ ≤ 4 := by omega
  have hunion : c.supp ∪ d.supp = (Set.univ : Set W) := by
    by_contra huniv
    have hlt_union : (c.supp ∪ d.supp).ncard < (Set.univ : Set W).ncard := by
      by_contra hnotlt_union
      have hEqUnion : c.supp ∪ d.supp = (Set.univ : Set W) := by
        apply Set.eq_of_subset_of_ncard_le
          (show c.supp ∪ d.supp ⊆ (Set.univ : Set W) by
            intro x hx
            simp)
        exact Nat.not_lt.mp hnotlt_union
      exact huniv hEqUnion
    obtain ⟨x, -, hx_not_union⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt_union
    let e : H.ConnectedComponent := H.connectedComponentMk x
    have hx_mem : x ∈ e.supp := by
      simpa [e] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := x))
    have hce : e ≠ c := by
      intro hec
      exact hx_not_union (Or.inl (hec ▸ hx_mem))
    have hed : e ≠ d := by
      intro hed'
      exact hx_not_union (Or.inr (hed' ▸ hx_mem))
    have hdisj_ce : Disjoint c.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hce.symm
    have hdisj_de : Disjoint d.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hed.symm
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
    have hunion_ge5 : 5 ≤ (c.supp ∪ d.supp).ncard := by
      rw [Set.ncard_union_eq hdisj]
      omega
    have hesubset : e.supp ⊆ (Set.univ : Set W) \ (c.supp ∪ d.supp) := by
      intro y hy
      refine ⟨by simp, ?_⟩
      intro hycd
      rcases hycd with hyc | hyd
      · exact Set.disjoint_left.mp hdisj_ce hyc hy
      · exact Set.disjoint_left.mp hdisj_de hyd hy
    have hele1 : e.supp.ncard ≤ 1 := by
      calc
        e.supp.ncard ≤ ((Set.univ : Set W) \ (c.supp ∪ d.supp)).ncard := Set.ncard_le_ncard hesubset
        _ = 6 - (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_diff (show c.supp ∪ d.supp ⊆ (Set.univ : Set W) by
            intro x hx
            simp)]
          simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
        _ ≤ 1 := by omega
    exact (show ¬ 3 ≤ 1 by decide) (hege3.trans hele1)
  exact ⟨d, by simpa [c] using hcd, by omega, hunion⟩

/-- Six-vertex path-plus-cycle classification for the degree pattern `1,1,2,...,2`: the endpoint
component is a path, and either it already covers all vertices or the remaining component is an
explicit `3`- or `4`-cycle.

Source: new support-level realization theorem for the seven-vertex `|E| = 16` profile
`(4,2,1)`. -/
theorem exists_path_covering_endpoint_component_and_cycle_component_case_split_of_card_eq_six_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hcard : Fintype.card W = 6)
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = (H.connectedComponentMk u).supp ∧
      (((H.connectedComponentMk u).supp = Set.univ) ∨
        ∃ d : H.ConnectedComponent, d ≠ H.connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
          (H.connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : W, ∃ q : H.Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp) := by
  classical
  rcases
      exists_path_covering_endpoint_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) huv hu1 hv1 hrest with
    ⟨p, hp, hpverts⟩
  refine ⟨p, hp, hpverts, ?_⟩
  by_cases hcov : (H.connectedComponentMk u).supp = Set.univ
  · exact Or.inl hcov
  · rcases
        exists_distinct_component_card_three_or_four_of_card_eq_six_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
          (H := H) hcard huv hu1 hv1 hrest hcov with
      ⟨d, hcd, hsize, hunion⟩
    rcases
        exists_cycle_covering_distinct_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
          (H := H) huv hu1 hv1 hrest hcd with
      ⟨x, q, hq, hqverts⟩
    exact Or.inr ⟨d, hcd, hsize, hunion, x, q, hq, hqverts⟩

end Generic

end FourColor.Curriculum.Actual
