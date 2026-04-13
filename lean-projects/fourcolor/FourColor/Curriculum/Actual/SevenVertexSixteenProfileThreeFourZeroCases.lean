import Mathlib.Data.Set.Card
import FourColor.Curriculum.Actual.SevenVertexSixteenProfileThreeFourZeroStructure

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- On seven vertices, two distinct path components whose endpoints account for all four degree-`1`
vertices force exactly one of the three complement shapes `P₂ ⊔ P₅`, `P₃ ⊔ P₄`, or
`P₂ ⊔ P₂ ⊔ C₃`.

Source: generic structural helper for the seven-vertex `|E| = 16` profile `(3,4,0)`. -/
theorem path_path_cycle_case_split_of_card_eq_seven_of_two_distinct_path_components_with_four_degree_one_vertices
    (hcard : Fintype.card W = 7)
    {c d : H.ConnectedComponent} (hcd : c ≠ d)
    {u₁ v₁ u₂ v₂ : W} (huv₁ : u₁ ≠ v₁) (huv₂ : u₂ ≠ v₂)
    (hu₁1 : H.degree u₁ = 1) (hv₁1 : H.degree v₁ = 1)
    (hu₂1 : H.degree u₂ = 1) (hv₂1 : H.degree v₂ = 1)
    (hrest : ∀ x : W, x ≠ u₁ → x ≠ v₁ → x ≠ u₂ → x ≠ v₂ → H.degree x = 2)
    {p : H.Walk u₁ v₁} (hp : p.IsPath) (hpverts : p.toSubgraph.verts = c.supp)
    {q : H.Walk u₂ v₂} (hq : q.IsPath) (hqverts : q.toSubgraph.verts = d.supp) :
    (c.supp.ncard = 2 ∧ d.supp.ncard = 5 ∧ c.supp ∪ d.supp = Set.univ) ∨
      (c.supp.ncard = 5 ∧ d.supp.ncard = 2 ∧ c.supp ∪ d.supp = Set.univ) ∨
      (c.supp.ncard = 3 ∧ d.supp.ncard = 4 ∧ c.supp ∪ d.supp = Set.univ) ∨
      (c.supp.ncard = 4 ∧ d.supp.ncard = 3 ∧ c.supp ∪ d.supp = Set.univ) ∨
      (c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧
        ∃ e : H.ConnectedComponent, e ≠ c ∧ e ≠ d ∧ e.supp.ncard = 3 ∧
          c.supp ∪ d.supp ∪ e.supp = Set.univ ∧
          ∃ x : W, ∃ r : H.Walk x x, r.IsCycle ∧ r.toSubgraph.verts = e.supp) := by
  classical
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hcd
  have hu₁c : u₁ ∈ c.supp := by
    have : u₁ ∈ p.toSubgraph.verts := p.start_mem_verts_toSubgraph
    exact hpverts ▸ this
  have hv₁c : v₁ ∈ c.supp := by
    have : v₁ ∈ p.toSubgraph.verts := p.end_mem_verts_toSubgraph
    exact hpverts ▸ this
  have hu₂d : u₂ ∈ d.supp := by
    have : u₂ ∈ q.toSubgraph.verts := q.start_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hv₂d : v₂ ∈ d.supp := by
    have : v₂ ∈ q.toSubgraph.verts := q.end_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hcge2 : 2 ≤ c.supp.ncard := by
    have hgt : 1 < c.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨u₁, hu₁c, v₁, hv₁c, huv₁⟩
    omega
  have hdge2 : 2 ≤ d.supp.ncard := by
    have hgt : 1 < d.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨u₂, hu₂d, v₂, hv₂d, huv₂⟩
    omega
  by_cases hcov : c.supp ∪ d.supp = Set.univ
  · have hsum : c.supp.ncard + d.supp.ncard = 7 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj_cd]
        _ = 7 := by rw [hcov, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    have hcases :
        (c.supp.ncard = 2 ∧ d.supp.ncard = 5) ∨
          (c.supp.ncard = 5 ∧ d.supp.ncard = 2) ∨
          (c.supp.ncard = 3 ∧ d.supp.ncard = 4) ∨
          (c.supp.ncard = 4 ∧ d.supp.ncard = 3) := by
      omega
    rcases hcases with h25 | h52 | h34 | h43
    · exact Or.inl ⟨h25.1, h25.2, hcov⟩
    · exact Or.inr <| Or.inl ⟨h52.1, h52.2, hcov⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨h34.1, h34.2, hcov⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h43.1, h43.2, hcov⟩
  · have hlt_union : (c.supp ∪ d.supp).ncard < (Set.univ : Set W).ncard := by
      by_contra hnotlt
      have hEq : c.supp ∪ d.supp = (Set.univ : Set W) := by
        apply Set.eq_of_subset_of_ncard_le
          (show c.supp ∪ d.supp ⊆ (Set.univ : Set W) by
            intro x hx
            simp)
        exact Nat.not_lt.mp hnotlt
      exact hcov hEq
    obtain ⟨w, _, hw_not_union⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt_union
    let e : H.ConnectedComponent := H.connectedComponentMk w
    have hw_e : w ∈ e.supp := by
      simpa [e] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := w))
    have hec : e ≠ c := by
      intro hEq
      exact hw_not_union (Or.inl (hEq ▸ hw_e))
    have hed : e ≠ d := by
      intro hEq
      exact hw_not_union (Or.inr (hEq ▸ hw_e))
    have hdisj_ce : Disjoint c.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hec.symm
    have hdisj_de : Disjoint d.supp e.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hed.symm
    have hedeg : ∀ x : W, x ∈ e.supp → H.degree x = 2 := by
      intro x hx
      have hxu₁ : x ≠ u₁ := by
        intro hEq
        exact Set.disjoint_left.mp hdisj_ce (hEq ▸ hu₁c) hx
      have hxv₁ : x ≠ v₁ := by
        intro hEq
        exact Set.disjoint_left.mp hdisj_ce (hEq ▸ hv₁c) hx
      have hxu₂ : x ≠ u₂ := by
        intro hEq
        exact Set.disjoint_left.mp hdisj_de (hEq ▸ hu₂d) hx
      have hxv₂ : x ≠ v₂ := by
        intro hEq
        exact Set.disjoint_left.mp hdisj_de (hEq ▸ hv₂d) hx
      exact hrest x hxu₁ hxv₁ hxu₂ hxv₂
    have hege3 : 3 ≤ e.supp.ncard :=
      connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) e hedeg
    have hdisj_cde : Disjoint (c.supp ∪ d.supp) e.supp := by
      rw [Set.disjoint_left]
      intro x hxcd hxe
      rcases hxcd with hxc | hxd
      · exact Set.disjoint_left.mp hdisj_ce hxc hxe
      · exact Set.disjoint_left.mp hdisj_de hxd hxe
    have hunion3_card_ge :
        7 ≤ (c.supp ∪ d.supp ∪ e.supp).ncard := by
      calc
        7 ≤ c.supp.ncard + d.supp.ncard + e.supp.ncard := by omega
        _ = (c.supp ∪ d.supp).ncard + e.supp.ncard := by
          rw [Set.ncard_union_eq hdisj_cd]
        _ = (c.supp ∪ d.supp ∪ e.supp).ncard := by
          simpa [Set.union_assoc] using (Set.ncard_union_eq hdisj_cde).symm
    have hunion3_le :
        (c.supp ∪ d.supp ∪ e.supp).ncard ≤ (Set.univ : Set W).ncard := by
      exact Set.ncard_le_ncard (by
        intro x hx
        simp)
    have hunion3_card :
        (c.supp ∪ d.supp ∪ e.supp).ncard = 7 := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] at hunion3_le
      exact Nat.le_antisymm hunion3_le hunion3_card_ge
    have hunion3 :
        c.supp ∪ d.supp ∪ e.supp = (Set.univ : Set W) := by
      apply Set.eq_of_subset_of_ncard_le
        (show c.supp ∪ d.supp ∪ e.supp ⊆ (Set.univ : Set W) by
          intro x hx
          simp)
      simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using hunion3_card.ge
    have hsum3 : c.supp.ncard + d.supp.ncard + e.supp.ncard = 7 := by
      calc
        c.supp.ncard + d.supp.ncard + e.supp.ncard =
            (c.supp ∪ d.supp).ncard + e.supp.ncard := by
          rw [Set.ncard_union_eq hdisj_cd]
        _ = (c.supp ∪ d.supp ∪ e.supp).ncard := by
          simpa [Set.union_assoc] using (Set.ncard_union_eq hdisj_cde).symm
        _ = 7 := hunion3_card
    have hcards : c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧ e.supp.ncard = 3 := by
      omega
    rcases
        exists_cycle_covering_connectedComponent_of_forall_degree_eq_two
          (H := H) e hedeg with
      ⟨x, r, hr, hrverts⟩
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      ⟨hcards.1, hcards.2.1, e, hec, hed, hcards.2.2, hunion3, x, r, hr, hrverts⟩

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Exact complement-shape split for the seven-vertex `|E| = 16` profile `(3,4,0)`:
`P₂ ⊔ P₅`, `P₃ ⊔ P₄`, or `P₂ ⊔ P₂ ⊔ C₃`.

Source: structural realization theorem for the last unresolved seven-vertex endpoint-heavy exact
`16`-edge branch. -/
theorem IsIncidenceCriticalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      c.supp.ncard = 2 ∧ d.supp.ncard = 5 ∧ c.supp ∪ d.supp = Set.univ ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
        c.supp.ncard = 3 ∧ d.supp.ncard = 4 ∧ c.supp ∪ d.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d e : (Gᶜ).ConnectedComponent, c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
        c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧ e.supp.ncard = 3 ∧
        c.supp ∪ d.supp ∪ e.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp ∧
        ∃ x : V, ∃ r : (Gᶜ).Walk x x, r.IsCycle ∧ r.toSubgraph.verts = e.supp) := by
  classical
  let H : SimpleGraph V := Gᶜ
  rcases
      h.exists_distinct_four_compl_degree_eq_one_card_support_eq_seven_forall_rest_degree_two_of_profile_three_four_zero
        hcard hedge hprof with
    ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha1, hb1, hc1, hd1, _hsupp, hrest⟩
  have hdeg_one_cases :
      ∀ {w : V}, H.degree w = 1 → w = a ∨ w = b ∨ w = c ∨ w = d := by
    intro w hw1
    by_cases hwa : w = a
    · exact Or.inl hwa
    · by_cases hwb : w = b
      · exact Or.inr <| Or.inl hwb
      · by_cases hwc : w = c
        · exact Or.inr <| Or.inr <| Or.inl hwc
        · by_cases hwd : w = d
          · exact Or.inr <| Or.inr <| Or.inr hwd
          · have hw2 : H.degree w = 2 := hrest w hwa hwb hwc hwd
            omega
  have hdeg12 : ∀ w : V, H.degree w = 1 ∨ H.degree w = 2 := by
    intro w
    by_cases hwa : w = a
    · subst w
      exact Or.inl ha1
    · by_cases hwb : w = b
      · subst w
        exact Or.inl hb1
      · by_cases hwc : w = c
        · subst w
          exact Or.inl hc1
        · by_cases hwd : w = d
          · subst w
            exact Or.inl hd1
          · exact Or.inr (hrest w hwa hwb hwc hwd)
  let c₁ : H.ConnectedComponent := H.connectedComponentMk a
  have ha_c₁ : a ∈ c₁.supp := by
    simpa [c₁] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := a))
  have hdeg_c₁ : ∀ w : V, w ∈ c₁.supp → H.degree w = 1 ∨ H.degree w = 2 := by
    intro w hw
    exact hdeg12 w
  rcases
      exists_partner_and_path_covering_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
        (H := H) c₁ ha_c₁ ha1 hdeg_c₁ with
    ⟨v₁, hv₁_c₁, hv₁a, hv₁1, hrest_c₁, p₁, hp₁, hp₁verts⟩
  have hv₁_cases : v₁ = b ∨ v₁ = c ∨ v₁ = d := by
    rcases hdeg_one_cases hv₁1 with hEq | hEq | hEq | hEq
    · exact False.elim (hv₁a hEq)
    · exact Or.inl hEq
    · exact Or.inr <| Or.inl hEq
    · exact Or.inr <| Or.inr hEq
  rcases hv₁_cases with hv₁b | hv₁c | hv₁d
  · subst v₁
    have hb_c₁ : b ∈ c₁.supp := by simpa using hv₁_c₁
    have hc_not_c₁ : c ∉ c₁.supp := by
      intro hc_c₁
      have hc2 : H.degree c = 2 := hrest_c₁ c hc_c₁ hac.symm hbc.symm
      exact (show (1 : ℕ) ≠ 2 by decide) (hc1.symm.trans hc2)
    have hd_not_c₁ : d ∉ c₁.supp := by
      intro hd_c₁
      have hd2 : H.degree d = 2 := hrest_c₁ d hd_c₁ had.symm hbd.symm
      exact (show (1 : ℕ) ≠ 2 by decide) (hd1.symm.trans hd2)
    let c₂ : H.ConnectedComponent := H.connectedComponentMk c
    have hc_c₂ : c ∈ c₂.supp := by
      simpa [c₂] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := c))
    have hc₂_ne_c₁ : c₂ ≠ c₁ := by
      intro hEq
      exact hc_not_c₁ (hEq ▸ hc_c₂)
    have hdeg_c₂ : ∀ w : V, w ∈ c₂.supp → H.degree w = 1 ∨ H.degree w = 2 := by
      intro w hw
      exact hdeg12 w
    rcases
        exists_partner_and_path_covering_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
          (H := H) c₂ hc_c₂ hc1 hdeg_c₂ with
      ⟨v₂, hv₂_c₂, hv₂c, hv₂1, hrest_c₂, p₂, hp₂, hp₂verts⟩
    have hv₂d : v₂ = d := by
      rcases hdeg_one_cases hv₂1 with hEq | hEq | hEq | hEq
      · have : a ∉ c₂.supp := by
          intro ha_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex ha_c₂ ha_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
      · have : b ∉ c₂.supp := by
          intro hb_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hb_c₂ hb_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
      · exact False.elim (hv₂c hEq)
      · exact hEq
    subst v₂
    rcases
        path_path_cycle_case_split_of_card_eq_seven_of_two_distinct_path_components_with_four_degree_one_vertices
          (H := H) hcard hc₂_ne_c₁.symm hab hcd ha1 hb1 hc1 hd1 hrest hp₁ hp₁verts hp₂ hp₂verts with
      h25 | h52 | h34 | h43 | h223
    · exact Or.inl ⟨c₁, c₂, hc₂_ne_c₁.symm, h25.1, h25.2.1, h25.2.2,
        a, b, hab, p₁, hp₁, hp₁verts, c, d, hcd, p₂, hp₂, hp₂verts⟩
    · exact Or.inl ⟨c₂, c₁, hc₂_ne_c₁, h52.2.1, h52.1, by simpa [Set.union_comm] using h52.2.2,
        c, d, hcd, p₂, hp₂, hp₂verts, a, b, hab, p₁, hp₁, hp₁verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₁, c₂, hc₂_ne_c₁.symm, h34.1, h34.2.1, h34.2.2,
          a, b, hab, p₁, hp₁, hp₁verts, c, d, hcd, p₂, hp₂, hp₂verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₂, c₁, hc₂_ne_c₁, h43.2.1, h43.1, by simpa [Set.union_comm] using h43.2.2,
          c, d, hcd, p₂, hp₂, hp₂verts, a, b, hab, p₁, hp₁, hp₁verts⟩
    · rcases h223 with ⟨hc2, hd2, e, hec, hed, he3, hunion, x, r, hr, hrverts⟩
      exact Or.inr <| Or.inr
        ⟨c₁, c₂, e, hc₂_ne_c₁.symm, hec.symm, hed.symm, hc2, hd2, he3, hunion,
          a, b, hab, p₁, hp₁, hp₁verts, c, d, hcd, p₂, hp₂, hp₂verts, x, r, hr, hrverts⟩
  · subst v₁
    have hc_c₁ : c ∈ c₁.supp := by simpa using hv₁_c₁
    have hb_not_c₁ : b ∉ c₁.supp := by
      intro hb_c₁
      have hb2 : H.degree b = 2 := hrest_c₁ b hb_c₁ hab.symm hbc
      exact (show (1 : ℕ) ≠ 2 by decide) (hb1.symm.trans hb2)
    have hd_not_c₁ : d ∉ c₁.supp := by
      intro hd_c₁
      have hd2 : H.degree d = 2 := hrest_c₁ d hd_c₁ had.symm hcd.symm
      exact (show (1 : ℕ) ≠ 2 by decide) (hd1.symm.trans hd2)
    let c₂ : H.ConnectedComponent := H.connectedComponentMk b
    have hb_c₂ : b ∈ c₂.supp := by
      simpa [c₂] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := b))
    have hc₂_ne_c₁ : c₂ ≠ c₁ := by
      intro hEq
      exact hb_not_c₁ (hEq ▸ hb_c₂)
    have hdeg_c₂ : ∀ w : V, w ∈ c₂.supp → H.degree w = 1 ∨ H.degree w = 2 := by
      intro w hw
      exact hdeg12 w
    rcases
        exists_partner_and_path_covering_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
          (H := H) c₂ hb_c₂ hb1 hdeg_c₂ with
      ⟨v₂, hv₂_c₂, hv₂b, hv₂1, hrest_c₂, p₂, hp₂, hp₂verts⟩
    have hv₂d : v₂ = d := by
      rcases hdeg_one_cases hv₂1 with hEq | hEq | hEq | hEq
      · have : a ∉ c₂.supp := by
          intro ha_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex ha_c₂ ha_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
      · exact False.elim (hv₂b hEq)
      · have : c ∉ c₂.supp := by
          intro hc_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hc_c₂ hc_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
      · exact hEq
    subst v₂
    rcases
        path_path_cycle_case_split_of_card_eq_seven_of_two_distinct_path_components_with_four_degree_one_vertices
          (H := H) hcard hc₂_ne_c₁.symm hac hbd ha1 hc1 hb1 hd1
          (fun x hxa hxc hxb hxd => by
            exact hrest x hxa hxb hxc hxd)
          hp₁ hp₁verts hp₂ hp₂verts with
      h25 | h52 | h34 | h43 | h223
    · exact Or.inl ⟨c₁, c₂, hc₂_ne_c₁.symm, h25.1, h25.2.1, h25.2.2,
        a, c, hac, p₁, hp₁, hp₁verts, b, d, hbd, p₂, hp₂, hp₂verts⟩
    · exact Or.inl ⟨c₂, c₁, hc₂_ne_c₁, h52.2.1, h52.1, by simpa [Set.union_comm] using h52.2.2,
        b, d, hbd, p₂, hp₂, hp₂verts, a, c, hac, p₁, hp₁, hp₁verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₁, c₂, hc₂_ne_c₁.symm, h34.1, h34.2.1, h34.2.2,
          a, c, hac, p₁, hp₁, hp₁verts, b, d, hbd, p₂, hp₂, hp₂verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₂, c₁, hc₂_ne_c₁, h43.2.1, h43.1, by simpa [Set.union_comm] using h43.2.2,
          b, d, hbd, p₂, hp₂, hp₂verts, a, c, hac, p₁, hp₁, hp₁verts⟩
    · rcases h223 with ⟨hc2, hd2, e, hec, hed, he3, hunion, x, r, hr, hrverts⟩
      exact Or.inr <| Or.inr
        ⟨c₁, c₂, e, hc₂_ne_c₁.symm, hec.symm, hed.symm, hc2, hd2, he3, hunion,
          a, c, hac, p₁, hp₁, hp₁verts, b, d, hbd, p₂, hp₂, hp₂verts, x, r, hr, hrverts⟩
  · subst v₁
    have hd_c₁ : d ∈ c₁.supp := by simpa using hv₁_c₁
    have hb_not_c₁ : b ∉ c₁.supp := by
      intro hb_c₁
      have hb2 : H.degree b = 2 := hrest_c₁ b hb_c₁ hab.symm hbd
      exact (show (1 : ℕ) ≠ 2 by decide) (hb1.symm.trans hb2)
    have hc_not_c₁ : c ∉ c₁.supp := by
      intro hc_c₁
      have hc2 : H.degree c = 2 := hrest_c₁ c hc_c₁ hac.symm hcd
      exact (show (1 : ℕ) ≠ 2 by decide) (hc1.symm.trans hc2)
    let c₂ : H.ConnectedComponent := H.connectedComponentMk b
    have hb_c₂ : b ∈ c₂.supp := by
      simpa [c₂] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := b))
    have hc₂_ne_c₁ : c₂ ≠ c₁ := by
      intro hEq
      exact hb_not_c₁ (hEq ▸ hb_c₂)
    have hdeg_c₂ : ∀ w : V, w ∈ c₂.supp → H.degree w = 1 ∨ H.degree w = 2 := by
      intro w hw
      exact hdeg12 w
    rcases
        exists_partner_and_path_covering_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
          (H := H) c₂ hb_c₂ hb1 hdeg_c₂ with
      ⟨v₂, hv₂_c₂, hv₂b, hv₂1, hrest_c₂, p₂, hp₂, hp₂verts⟩
    have hv₂c : v₂ = c := by
      rcases hdeg_one_cases hv₂1 with hEq | hEq | hEq | hEq
      · have : a ∉ c₂.supp := by
          intro ha_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex ha_c₂ ha_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
      · exact False.elim (hv₂b hEq)
      · exact hEq
      · have : d ∉ c₂.supp := by
          intro hd_c₂
          exact hc₂_ne_c₁ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hd_c₂ hd_c₁)
        exact False.elim (this (hEq ▸ hv₂_c₂))
    subst v₂
    rcases
        path_path_cycle_case_split_of_card_eq_seven_of_two_distinct_path_components_with_four_degree_one_vertices
          (H := H) hcard hc₂_ne_c₁.symm had hbc ha1 hd1 hb1 hc1
          (fun x hxa hxd hxb hxc => by
            exact hrest x hxa hxb hxc hxd)
          hp₁ hp₁verts hp₂ hp₂verts with
      h25 | h52 | h34 | h43 | h223
    · exact Or.inl ⟨c₁, c₂, hc₂_ne_c₁.symm, h25.1, h25.2.1, h25.2.2,
        a, d, had, p₁, hp₁, hp₁verts, b, c, hbc, p₂, hp₂, hp₂verts⟩
    · exact Or.inl ⟨c₂, c₁, hc₂_ne_c₁, h52.2.1, h52.1, by simpa [Set.union_comm] using h52.2.2,
        b, c, hbc, p₂, hp₂, hp₂verts, a, d, had, p₁, hp₁, hp₁verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₁, c₂, hc₂_ne_c₁.symm, h34.1, h34.2.1, h34.2.2,
          a, d, had, p₁, hp₁, hp₁verts, b, c, hbc, p₂, hp₂, hp₂verts⟩
    · exact Or.inr <| Or.inl
        ⟨c₂, c₁, hc₂_ne_c₁, h43.2.1, h43.1, by simpa [Set.union_comm] using h43.2.2,
          b, c, hbc, p₂, hp₂, hp₂verts, a, d, had, p₁, hp₁, hp₁verts⟩
    · rcases h223 with ⟨hc2, hd2, e, hec, hed, he3, hunion, x, r, hr, hrverts⟩
      exact Or.inr <| Or.inr
        ⟨c₁, c₂, e, hc₂_ne_c₁.symm, hec.symm, hed.symm, hc2, hd2, he3, hunion,
          a, d, had, p₁, hp₁, hp₁verts, b, c, hbc, p₂, hp₂, hp₂verts, x, r, hr, hrverts⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the exact `(3,4,0)` complement-shape split. -/
theorem IsVertexCriticalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      c.supp.ncard = 2 ∧ d.supp.ncard = 5 ∧ c.supp ∪ d.supp = Set.univ ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
        c.supp.ncard = 3 ∧ d.supp.ncard = 4 ∧ c.supp ∪ d.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d e : (Gᶜ).ConnectedComponent, c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
        c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧ e.supp.ncard = 3 ∧
        c.supp ∪ d.supp ∪ e.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp ∧
        ∃ x : V, ∃ r : (Gᶜ).Walk x x, r.IsCycle ∧ r.toSubgraph.verts = e.supp) := by
  exact
    IsIncidenceCriticalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge hprof

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the exact `(3,4,0)` complement-shape split. -/
theorem IsMinimalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      c.supp.ncard = 2 ∧ d.supp.ncard = 5 ∧ c.supp ∪ d.supp = Set.univ ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
        c.supp.ncard = 3 ∧ d.supp.ncard = 4 ∧ c.supp ∪ d.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d e : (Gᶜ).ConnectedComponent, c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
        c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧ e.supp.ncard = 3 ∧
        c.supp ∪ d.supp ∪ e.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp ∧
        ∃ x : V, ∃ r : (Gᶜ).Walk x x, r.IsCycle ∧ r.toSubgraph.verts = e.supp) := by
  exact
    IsIncidenceCriticalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free exact `(3,4,0)`
complement-shape split without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      c.supp.ncard = 2 ∧ d.supp.ncard = 5 ∧ c.supp ∪ d.supp = Set.univ ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
        c.supp.ncard = 3 ∧ d.supp.ncard = 4 ∧ c.supp ∪ d.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp) ∨
      (∃ c d e : (Gᶜ).ConnectedComponent, c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
        c.supp.ncard = 2 ∧ d.supp.ncard = 2 ∧ e.supp.ncard = 3 ∧
        c.supp ∪ d.supp ∪ e.supp = Set.univ ∧
        ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
          ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
        ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
          ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp ∧
        ∃ x : V, ∃ r : (Gᶜ).Walk x x, r.IsCycle ∧ r.toSubgraph.verts = e.supp) := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.compl_path_path_cycle_case_split_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

end MinimalBridge

end FourColor.Curriculum.Actual
