import FourColor.Curriculum.Actual.SevenVertexCycleCases

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A finite connected `2`-regular graph is realized by a single cycle whose support is all
vertices.

Source: new theorem packaging Mathlib's component-cycle extraction into the exact form needed for
the connected seven-vertex complement branch. -/
theorem exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree 2) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  let v : V := Classical.choice (show Nonempty V from hconn.2)
  let c : G.ConnectedComponent := G.connectedComponentMk v
  have hv : v ∈ c.supp := by
    simpa [c] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := v))
  have hsupp : c.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change G.connectedComponentMk w = G.connectedComponentMk v
    exact (SimpleGraph.ConnectedComponent.eq (G := G) (v := w) (w := v)).2
      ((hconn.1 v w).symm)
  have hcyc : G.IsCycles := isCycles_of_isRegularOfDegree_two hreg
  have hdeg_pos : 0 < G.degree v := by simp [hreg v]
  have hneigh : (G.neighborSet v).Nonempty := by
    rcases (G.degree_pos_iff_exists_adj v).1 hdeg_pos with ⟨w, hw⟩
    exact ⟨w, hw⟩
  rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := c) hv hneigh with
    ⟨p, hpcycle, hpverts⟩
  refine ⟨v, p, hpcycle, ?_⟩
  simpa [hsupp] using hpverts

/-- A finite disconnected `2`-regular graph on seven vertices has distinct connected components of
sizes `3` and `4`.

Source: new theorem refining the disconnected branch of the seven-vertex `2`-regular
classification. -/
theorem exists_distinct_components_card_three_four_of_not_connected_of_card_eq_seven_of_isRegularOfDegree_two
    (hnot : ¬ G.Connected) (hcard : Fintype.card V = 7) (hreg : G.IsRegularOfDegree 2) :
    ∃ c d : G.ConnectedComponent, c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 4 := by
  rcases connected_or_exists_component_card_three_of_card_eq_seven_of_isRegularOfDegree_two
      (G := G) hcard hreg with hconn | ⟨c, hc3⟩
  · exact False.elim (hnot hconn)
  have hlt : c.supp.ncard < (Set.univ : Set V).ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hc3]
    decide
  obtain ⟨v, -, hvnotc⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  let d : G.ConnectedComponent := G.connectedComponentMk v
  have hvd : v ∈ d.supp := by
    simpa [d] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := v))
  have hcd : c ≠ d := by
    intro hcd
    exact hvnotc (hcd ▸ hvd)
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := G)) hcd
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg d
  have hdsubset : d.supp ⊆ Set.univ \ c.supp := by
    intro x hx
    refine ⟨by simp, ?_⟩
    exact Set.disjoint_right.mp hdisj_cd hx
  have hdle4 : d.supp.ncard ≤ 4 := by
    calc
      d.supp.ncard ≤ (Set.univ \ c.supp).ncard := Set.ncard_le_ncard hdsubset
      _ = 4 := by
        rw [Set.ncard_diff (show c.supp ⊆ (Set.univ : Set V) by intro x hx; simp)]
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hc3]
  have hne3 : d.supp.ncard ≠ 3 := by
    intro hd3
    have hunion6 : (c.supp ∪ d.supp).ncard = 6 := by
      rw [Set.ncard_union_eq hdisj_cd]
      simp [hc3, hd3]
    have hlt_union : (c.supp ∪ d.supp).ncard < (Set.univ : Set V).ncard := by
      rw [hunion6, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      decide
    obtain ⟨u, -, huout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt_union
    let e : G.ConnectedComponent := G.connectedComponentMk u
    have hue : u ∈ e.supp := by
      simpa [e] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := u))
    have hce : c ≠ e := by
      intro hce
      exact huout (Or.inl (hce ▸ hue))
    have hde : d ≠ e := by
      intro hde
      exact huout (Or.inr (hde ▸ hue))
    have hdisj_ce : Disjoint c.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := G)) hce
    have hdisj_de : Disjoint d.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := G)) hde
    have hesubset : e.supp ⊆ Set.univ \ (c.supp ∪ d.supp) := by
      intro x hx
      refine ⟨by simp, ?_⟩
      refine not_or_intro ?_ ?_
      · exact Set.disjoint_right.mp hdisj_ce hx
      · exact Set.disjoint_right.mp hdisj_de hx
    have hele1 : e.supp.ncard ≤ 1 := by
      calc
        e.supp.ncard ≤ (Set.univ \ (c.supp ∪ d.supp)).ncard := Set.ncard_le_ncard hesubset
        _ = 1 := by
          rw [Set.ncard_diff (show c.supp ∪ d.supp ⊆ (Set.univ : Set V) by intro x hx; simp)]
          simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hunion6]
    have hege3 : 3 ≤ e.supp.ncard :=
      connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg e
    exact (show ¬ 3 ≤ 1 by decide) (hege3.trans hele1)
  have hd4 : d.supp.ncard = 4 := by omega
  exact ⟨c, d, hcd, hc3, hd4⟩

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the connected branch of the sharp seven-vertex low-edge case, the complement is realized by
a single cycle covering all vertices.

Source: new specialization of the generic connected `2`-regular realization theorem. -/
theorem IsIncidenceCriticalNonColorable.compl_exists_cycle_covering_all_vertices_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14)
    (hconn : Gᶜ.Connected) :
    ∃ (v : V) (p : (Gᶜ).Walk v v), p.IsCycle ∧ p.toSubgraph.verts = Set.univ := by
  exact exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
    (G := Gᶜ) hconn
    (h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge)

/-- In the disconnected branch of the sharp seven-vertex low-edge case, the complement has
distinct connected components of sizes `3` and `4`.

Source: new specialization of the generic disconnected seven-vertex `2`-regular realization
theorem. -/
theorem IsIncidenceCriticalNonColorable.compl_exists_distinct_components_card_three_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14)
    (hnot : ¬ Gᶜ.Connected) :
    ∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 4 := by
  exact exists_distinct_components_card_three_four_of_not_connected_of_card_eq_seven_of_isRegularOfDegree_two
    (G := Gᶜ) hnot hcard
    (h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge)

end IncidenceBranch

end FourColor.Curriculum.Actual
