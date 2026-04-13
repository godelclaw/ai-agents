import FourColor.Curriculum.Actual.SevenVertexFifteenComplement
import FourColor.Curriculum.Actual.SevenVertexCycleCases

namespace FourColor.Curriculum.Actual

section GenericTwoRegular

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- A disconnected `2`-regular graph on six vertices has exactly two distinct connected components,
each of cardinality `3`.

Source: new theorem for the isolated-support half of the seven-vertex `15`-edge branch. Every
connected component of a `2`-regular graph has size at least `3`, so two disjoint components in a
six-vertex graph must already exhaust all vertices. -/
theorem exists_distinct_components_card_three_three_of_not_connected_of_card_eq_six_of_isRegularOfDegree_two
    (hnot : ¬ H.Connected) (hcard : Fintype.card W = 6) (hreg : H.IsRegularOfDegree 2) :
    ∃ c d : H.ConnectedComponent, c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 3 := by
  classical
  have hpos : 0 < Fintype.card W := by omega
  let v : W := Classical.choice (Fintype.card_pos_iff.mp hpos)
  let c : H.ConnectedComponent := H.connectedComponentMk v
  have hcle6 : c.supp.ncard ≤ 6 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (Set.ncard_le_ncard (show c.supp ⊆ Set.univ by intro x hx; simp))
  have hclt6 : c.supp.ncard < 6 := by
    by_contra hnotlt
    have hc6 : c.supp.ncard = 6 := Nat.le_antisymm hcle6 (Nat.not_lt.mp hnotlt)
    exact hnot (connected_of_connectedComponent_ncard_eq_card (G := H) c (by simpa [hcard] using hc6))
  have hclt_univ : c.supp.ncard < (Set.univ : Set W).ncard := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using hclt6
  obtain ⟨u, -, hunotc⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hclt_univ
  let d : H.ConnectedComponent := H.connectedComponentMk u
  have hud : u ∈ d.supp := by
    simpa [d] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := u))
  have hcd : c ≠ d := by
    intro hEq
    exact hunotc (hEq ▸ hud)
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hcd
  have hcge3 : 3 ≤ c.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg c
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg d
  have hunion_le6 : (c.supp ∪ d.supp).ncard ≤ 6 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (Set.ncard_le_ncard (show c.supp ∪ d.supp ⊆ Set.univ by intro x hx; simp))
  have hsum_le6 : c.supp.ncard + d.supp.ncard ≤ 6 := by
    rwa [Set.ncard_union_eq hdisj] at hunion_le6
  have hsum_ge6 : 6 ≤ c.supp.ncard + d.supp.ncard := by omega
  have hc3 : c.supp.ncard = 3 := by omega
  have hd3 : d.supp.ncard = 3 := by omega
  exact ⟨c, d, hcd, hc3, hd3⟩

/-- A `2`-regular graph on six vertices is either connected or has exactly two distinct connected
components of cardinality `3`.

Source: new six-vertex support classification for the isolated-support half of the seven-vertex
`15`-edge branch. -/
theorem connected_or_exists_distinct_components_card_three_three_of_card_eq_six_of_isRegularOfDegree_two
    (hcard : Fintype.card W = 6) (hreg : H.IsRegularOfDegree 2) :
    H.Connected ∨
      ∃ c d : H.ConnectedComponent, c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 3 := by
  by_cases hconn : H.Connected
  · exact Or.inl hconn
  · exact Or.inr
      (exists_distinct_components_card_three_three_of_not_connected_of_card_eq_six_of_isRegularOfDegree_two
        (H := H) hconn hcard hreg)

end GenericTwoRegular

section ComplementSupport

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the complement support has cardinality `6` and is `2`-regular, then it is either connected
or it has exactly two distinct connected components of cardinality `3`.

Source: new specialization of the generic six-vertex `2`-regular classification to complement
support graphs. -/
theorem compl_support_connected_or_exists_distinct_components_card_three_three
    (hsupp : Fintype.card Gᶜ.support = 6)
    (hreg : ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ((Gᶜ).induce (Gᶜ.support)).Connected ∨
      ∃ c d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
        c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 3 := by
  exact
    connected_or_exists_distinct_components_card_three_three_of_card_eq_six_of_isRegularOfDegree_two
      (H := (Gᶜ).induce (Gᶜ.support)) hsupp hreg

/-- Branch-local wrapper for the isolated-support half of the seven-vertex `15`-edge complement
split. -/
theorem isolated_compl_support_connected_or_exists_distinct_components_card_three_three
    (hiso : ∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ((Gᶜ).induce (Gᶜ.support)).Connected ∨
      ∃ c d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent,
        c ≠ d ∧ c.supp.ncard = 3 ∧ d.supp.ncard = 3 := by
  rcases hiso with ⟨_, _, hsupp, hreg⟩
  exact compl_support_connected_or_exists_distinct_components_card_three_three
    (G := G) hsupp hreg

end ComplementSupport

end FourColor.Curriculum.Actual
