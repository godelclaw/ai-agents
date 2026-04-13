import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexDisconnectedColoring
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointConnectedColoring
import FourColor.Curriculum.Actual.SevenVertexRefinedBounds
import FourColor.Curriculum.Actual.SevenVertexEighteenExclusion

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A path whose associated subgraph has vertex set `s` has length `s.ncard - 1`.

Source: helper theorem for the remaining disconnected seven-vertex `15`-edge endpoint branch. It
extracts the exact path size from the endpoint-component realization. -/
theorem SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq
    {s : Set V} {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hverts : p.toSubgraph.verts = s) :
    p.length = s.ncard - 1 := by
  letI : Fintype s := (Set.toFinite s).fintype
  let f : Fin (p.length + 1) → s := fun i => ⟨p.getVert i, by
    have hxsupp : p.getVert i ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
        ⟨i, rfl, Nat.le_of_lt_succ i.is_lt⟩
    have hxverts : p.getVert i ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hxsupp
    rw [← hverts]
    exact hxverts⟩
  have hle' : p.length + 1 ≤ Fintype.card s := by
    simpa using Fintype.card_le_of_injective f (by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by simpa using Nat.le_of_lt_succ i.is_lt)
        (by simpa using Nat.le_of_lt_succ j.is_lt) (congrArg Subtype.val hij))
  have hge' : Fintype.card s ≤ p.length + 1 := by
    simpa using Fintype.card_le_of_surjective f (by
      intro x
      have hxverts : (x : V) ∈ p.toSubgraph.verts := by
        rw [hverts]
        exact x.property
      have hxsupp : (x : V) ∈ p.support := p.mem_verts_toSubgraph.mp hxverts
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
      refine ⟨⟨n, Nat.lt_succ_of_le hn⟩, ?_⟩
      exact Subtype.ext hxn)
  have hs_card : Fintype.card s = s.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hle : p.length + 1 ≤ s.ncard := by simpa [hs_card] using hle'
  have hge : s.ncard ≤ p.length + 1 := by simpa [hs_card] using hge'
  have hEq : s.ncard = p.length + 1 := Nat.le_antisymm hge hle
  omega

/-- If the complement splits as a `4`-vertex path component and a `3`-vertex cycle component,
then the original graph is `4`-colorable.

Source: new theorem closing the `P₄ ⊔ C₃` branch of the remaining seven-vertex `15`-edge
endpoint case. The `C₃` component is colored uniformly and the path is colored by its two
adjacent pairs. -/
theorem colorable_four_of_compl_path_component_card_four_and_cycle_component_card_three
    (hcard : Fintype.card V = 7)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp)
    {d : (Gᶜ).ConnectedComponent} (hcd : d ≠ (Gᶜ).connectedComponentMk u)
    (hd3 : d.supp.ncard = 3)
    (hunion : ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ)
    {x : V} {q : (Gᶜ).Walk x x} (hq : q.IsCycle) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  let c : (Gᶜ).ConnectedComponent := (Gᶜ).connectedComponentMk u
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ))
      (by simpa [c] using hcd.symm)
  have hc4 : c.supp.ncard = 4 := by
    have hsum : c.supp.ncard + d.supp.ncard = 7 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj]
        _ = 7 := by
          rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    omega
  have hlenp : p.length = 3 := by
    simpa [hpverts, c, hc4] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 3 := by
    simpa [hd3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let a3 : V := p.getVert 3
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  have hgetp_ne :
      ∀ {m n : ℕ}, m ≤ 3 → n ≤ 3 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hp.getVert_injOn (by simpa [hlenp] using hm) (by simpa [hlenp] using hn) hEq
  have ha20 : a2 ≠ a0 := by
    simpa [a2, a0] using hgetp_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have ha21 : a2 ≠ a1 := by
    simpa [a2, a1] using hgetp_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have ha30 : a3 ≠ a0 := by
    simpa [a3, a0] using hgetp_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have ha31 : a3 ≠ a1 := by
    simpa [a3, a1] using hgetp_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have hb01 : (Gᶜ).Adj b0 b1 := by
    have h0 : 0 < q.length := by omega
    simpa [b0, b1] using q.adj_getVert_succ h0
  have hb12 : (Gᶜ).Adj b1 b2 := by
    have h1 : 1 < q.length := by omega
    simpa [b1, b2] using q.adj_getVert_succ h1
  have hb20 : (Gᶜ).Adj b2 b0 := by
    have h2 : 2 < q.length := by omega
    have hb20' : (Gᶜ).Adj (q.getVert 2) (q.getVert q.length) := by
      simpa [hlenq] using q.adj_getVert_succ h2
    simpa [b2, b0, q.getVert_zero, q.getVert_length] using hb20'
  have ha01 : (Gᶜ).Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have ha23 : (Gᶜ).Adj a2 a3 := by
    have h2 : 2 < p.length := by omega
    simpa [a2, a3] using p.adj_getVert_succ h2
  have ha0mem : a0 ∈ c.supp := by
    have : a0 ∈ p.toSubgraph.verts := by simpa [a0] using p.start_mem_verts_toSubgraph
    exact hpverts ▸ this
  have ha1mem : a1 ∈ c.supp := by
    have hsupp : a1 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [a1], by omega⟩
    have : a1 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have ha2mem : a2 ∈ c.supp := by
    have hsupp : a2 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [a2], by omega⟩
    have : a2 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have ha3mem : a3 ∈ c.supp := by
    have hsupp : a3 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [a3], by omega⟩
    have : a3 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have hb0mem : b0 ∈ d.supp := by
    have : b0 ∈ q.toSubgraph.verts := by simpa [b0] using q.start_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hb1mem : b1 ∈ d.supp := by
    have hsupp : b1 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [b1], by omega⟩
    have : b1 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb2mem : b2 ∈ d.supp := by
    have hsupp : b2 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [b2], by omega⟩
    have : b2 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have ha0notd : a0 ∉ d.supp := Set.disjoint_left.mp hdisj ha0mem
  have ha1notd : a1 ∉ d.supp := Set.disjoint_left.mp hdisj ha1mem
  have ha2notd : a2 ∉ d.supp := Set.disjoint_left.mp hdisj ha2mem
  have ha3notd : a3 ∉ d.supp := Set.disjoint_left.mp hdisj ha3mem
  have hcover_c {y : V} (hy : y ∈ c.supp) : y = a0 ∨ y = a1 ∨ y = a2 ∨ y = a3 := by
    have hysupp : y ∈ p.support := by
      have hyverts : y ∈ p.toSubgraph.verts := hpverts.symm ▸ hy
      exact p.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlenp] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [a0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [a2] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr (by simpa [a3] using hyn.symm)
  have hcover_d {y : V} (hy : y ∈ d.supp) : y = b0 ∨ y = b1 ∨ y = b2 := by
    have hysupp : y ∈ q.support := by
      have hyverts : y ∈ q.toSubgraph.verts := hqverts.symm ▸ hy
      exact q.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlenq] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [b0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [b1] using hyn.symm)
    · exact Or.inr <| Or.inr (by simpa [b2] using hyn.symm)
    · exact Or.inl <| by
        calc
          y = q.getVert 3 := hyn.symm
          _ = q.getVert q.length := by simpa [hlenq]
          _ = q.getVert 0 := by rw [q.getVert_length, q.getVert_zero]
          _ = b0 := rfl
  have hcover :
      ∀ y : V, y ∈ d.supp ∨ y = a0 ∨ y = a1 ∨ y = a2 ∨ y = a3 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · rcases hcover_c hyc with rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
    · exact Or.inl hyd
  have htri {y z : V} (hy : y ∈ d.supp) (hz : z ∈ d.supp) (hyz : y ≠ z) : (Gᶜ).Adj y z := by
    rcases hcover_d hy with rfl | rfl | rfl
    · rcases hcover_d hz with rfl | rfl | rfl
      · exact False.elim (hyz rfl)
      · exact hb01
      · exact hb20.symm
    · rcases hcover_d hz with rfl | rfl | rfl
      · exact hb01.symm
      · exact False.elim (hyz rfl)
      · exact hb12
    · rcases hcover_d hz with rfl | rfl | rfl
      · exact hb20
      · exact hb12.symm
      · exact False.elim (hyz rfl)
  let color : V → Fin 4 := fun y =>
    if y ∈ d.supp then 0
    else if y = a0 ∨ y = a1 then 1
    else if y = a2 ∨ y = a3 then 2
    else 3
  have hcolor_d {y : V} (hy : y ∈ d.supp) : color y = 0 := by
    change
      (if y ∈ d.supp then 0 else if y = a0 ∨ y = a1 then 1 else if y = a2 ∨ y = a3 then 2
        else 3) = 0
    rw [if_pos hy]
  have hcolor_a0 : color a0 = 1 := by
    change
      (if a0 ∈ d.supp then 0 else if a0 = a0 ∨ a0 = a1 then 1 else if a0 = a2 ∨ a0 = a3 then 2
        else 3) = 1
    rw [if_neg ha0notd, if_pos (Or.inl rfl)]
  have hcolor_a1 : color a1 = 1 := by
    change
      (if a1 ∈ d.supp then 0 else if a1 = a0 ∨ a1 = a1 then 1 else if a1 = a2 ∨ a1 = a3 then 2
        else 3) = 1
    rw [if_neg ha1notd, if_pos (Or.inr rfl)]
  have hcolor_a2 : color a2 = 2 := by
    change
      (if a2 ∈ d.supp then 0 else if a2 = a0 ∨ a2 = a1 then 1 else if a2 = a2 ∨ a2 = a3 then 2
        else 3) = 2
    rw [if_neg ha2notd, if_neg (by
      intro h
      rcases h with h | h
      · exact ha20 h
      · exact ha21 h), if_pos (Or.inl rfl)]
  have hcolor_a3 : color a3 = 2 := by
    change
      (if a3 ∈ d.supp then 0 else if a3 = a0 ∨ a3 = a1 then 1 else if a3 = a2 ∨ a3 = a3 then 2
        else 3) = 2
    rw [if_neg ha3notd, if_neg (by
      intro h
      rcases h with h | h
      · exact ha30 h
      · exact ha31 h), if_pos (Or.inr rfl)]
  have bucket0 {y : V} (hy : color y = 0) : y ∈ d.supp := by
    rcases hcover y with hyd | rfl | rfl | rfl | rfl
    · exact hyd
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hy
      exact False.elim this
  have bucket1 {y : V} (hy : color y = 1) : y = a0 ∨ y = a1 := by
    rcases hcover y with hyd | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_d hyd] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y = a2 ∨ y = a3 := by
    rcases hcover y with hyd | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_d hyd] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      exact ((SimpleGraph.compl_adj G y z).1 (htri (bucket0 hy0) (bucket0 hz0) (G.ne_of_adj hyz))).2 hyz
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rcases bucket1 hy1 with hya0 | hya1
        · subst y
          rcases bucket1 hz1 with hza0 | hza1
          · subst z
            exact (G.ne_of_adj hyz) rfl
          · subst z
            exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
        · subst y
          rcases bucket1 hz1 with hza0 | hza1
          · subst z
            exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
          · subst z
            exact (G.ne_of_adj hyz) rfl
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with hya2 | hya3
          · subst y
            rcases bucket2 hz2 with hza2 | hza3
            · subst z
              exact (G.ne_of_adj hyz) rfl
            · subst z
              exact ((SimpleGraph.compl_adj G a2 a3).1 ha23).2 hyz
          · subst y
            rcases bucket2 hz2 with hza2 | hza3
            · subst z
              exact ((SimpleGraph.compl_adj G a3 a2).1 ha23.symm).2 hyz
            · subst z
              exact (G.ne_of_adj hyz) rfl
        · exfalso
          rcases hcover y with hyd | rfl | rfl | rfl | rfl
          · exact hy0 (hcolor_d hyd)
          · exact hy1 hcolor_a0
          · exact hy1 hcolor_a1
          · exact hy2 hcolor_a2
          · exact hy2 hcolor_a3
  exact hcolor.colorable

/-- If the complement splits as a `3`-vertex path component and a `4`-vertex cycle component,
then the original graph is `4`-colorable.

Source: new theorem closing the `P₃ ⊔ C₄` branch of the remaining seven-vertex `15`-edge
endpoint case. The path contributes one adjacent pair and one singleton, and the cycle contributes
two adjacent pairs. -/
theorem colorable_four_of_compl_path_component_card_three_and_cycle_component_card_four
    (hcard : Fintype.card V = 7)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp)
    {d : (Gᶜ).ConnectedComponent} (hcd : d ≠ (Gᶜ).connectedComponentMk u)
    (hd4 : d.supp.ncard = 4)
    (hunion : ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ)
    {x : V} {q : (Gᶜ).Walk x x} (hq : q.IsCycle) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  let c : (Gᶜ).ConnectedComponent := (Gᶜ).connectedComponentMk u
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ))
      (by simpa [c] using hcd.symm)
  have hc3 : c.supp.ncard = 3 := by
    have hsum : c.supp.ncard + d.supp.ncard = 7 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj]
        _ = 7 := by
          rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    omega
  have hlenp : p.length = 2 := by
    simpa [hpverts, c, hc3] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 4 := by
    simpa [hd4] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  let b3 : V := q.getVert 3
  have hgetp_ne :
      ∀ {m n : ℕ}, m ≤ 2 → n ≤ 2 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hp.getVert_injOn (by simpa [hlenp] using hm) (by simpa [hlenp] using hn) hEq
  have ha20 : a2 ≠ a0 := by
    simpa [a2, a0] using hgetp_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have ha21 : a2 ≠ a1 := by
    simpa [a2, a1] using hgetp_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have hgetq_ne :
      ∀ {m n : ℕ}, m ≤ 3 → n ≤ 3 → m ≠ n → q.getVert m ≠ q.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ q.length - 1 := by omega
    have hn' : n ≤ q.length - 1 := by omega
    apply hmn
    exact hq.getVert_injOn' hm' hn' hEq
  have hb20 : b2 ≠ b0 := by
    simpa [b2, b0] using hgetq_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have hb21 : b2 ≠ b1 := by
    simpa [b2, b1] using hgetq_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have hb30 : b3 ≠ b0 := by
    simpa [b3, b0] using hgetq_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have hb31 : b3 ≠ b1 := by
    simpa [b3, b1] using hgetq_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have ha01 : (Gᶜ).Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have hb01 : (Gᶜ).Adj b0 b1 := by
    have h0 : 0 < q.length := by omega
    simpa [b0, b1] using q.adj_getVert_succ h0
  have hb23 : (Gᶜ).Adj b2 b3 := by
    have h2 : 2 < q.length := by omega
    simpa [b2, b3] using q.adj_getVert_succ h2
  have ha0mem : a0 ∈ c.supp := by
    have : a0 ∈ p.toSubgraph.verts := by simpa [a0] using p.start_mem_verts_toSubgraph
    exact hpverts ▸ this
  have ha1mem : a1 ∈ c.supp := by
    have hsupp : a1 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [a1], by omega⟩
    have : a1 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have ha2mem : a2 ∈ c.supp := by
    have hsupp : a2 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [a2], by omega⟩
    have : a2 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have hb0mem : b0 ∈ d.supp := by
    have : b0 ∈ q.toSubgraph.verts := by simpa [b0] using q.start_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hb1mem : b1 ∈ d.supp := by
    have hsupp : b1 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [b1], by omega⟩
    have : b1 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb2mem : b2 ∈ d.supp := by
    have hsupp : b2 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [b2], by omega⟩
    have : b2 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb3mem : b3 ∈ d.supp := by
    have hsupp : b3 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [b3], by omega⟩
    have : b3 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have ha0notd : a0 ∉ d.supp := Set.disjoint_left.mp hdisj ha0mem
  have ha1notd : a1 ∉ d.supp := Set.disjoint_left.mp hdisj ha1mem
  have ha2notd : a2 ∉ d.supp := Set.disjoint_left.mp hdisj ha2mem
  have hb0notc : b0 ∉ c.supp := Set.disjoint_right.mp hdisj hb0mem
  have hb1notc : b1 ∉ c.supp := Set.disjoint_right.mp hdisj hb1mem
  have hb2notc : b2 ∉ c.supp := Set.disjoint_right.mp hdisj hb2mem
  have hb3notc : b3 ∉ c.supp := Set.disjoint_right.mp hdisj hb3mem
  have hb0a0 : b0 ≠ a0 := by intro hEq; exact hb0notc (hEq.symm ▸ ha0mem)
  have hb0a1 : b0 ≠ a1 := by intro hEq; exact hb0notc (hEq.symm ▸ ha1mem)
  have hb0a2 : b0 ≠ a2 := by intro hEq; exact hb0notc (hEq.symm ▸ ha2mem)
  have hb1a0 : b1 ≠ a0 := by intro hEq; exact hb1notc (hEq.symm ▸ ha0mem)
  have hb1a1 : b1 ≠ a1 := by intro hEq; exact hb1notc (hEq.symm ▸ ha1mem)
  have hb1a2 : b1 ≠ a2 := by intro hEq; exact hb1notc (hEq.symm ▸ ha2mem)
  have hb2a0 : b2 ≠ a0 := by intro hEq; exact hb2notc (hEq.symm ▸ ha0mem)
  have hb2a1 : b2 ≠ a1 := by intro hEq; exact hb2notc (hEq.symm ▸ ha1mem)
  have hb2a2 : b2 ≠ a2 := by intro hEq; exact hb2notc (hEq.symm ▸ ha2mem)
  have hb3a0 : b3 ≠ a0 := by intro hEq; exact hb3notc (hEq.symm ▸ ha0mem)
  have hb3a1 : b3 ≠ a1 := by intro hEq; exact hb3notc (hEq.symm ▸ ha1mem)
  have hb3a2 : b3 ≠ a2 := by intro hEq; exact hb3notc (hEq.symm ▸ ha2mem)
  have hcover_c {y : V} (hy : y ∈ c.supp) : y = a0 ∨ y = a1 ∨ y = a2 := by
    have hysupp : y ∈ p.support := by
      have hyverts : y ∈ p.toSubgraph.verts := hpverts.symm ▸ hy
      exact p.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn2 : n ≤ 2 := by simpa [hlenp] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl (by simpa [a0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1] using hyn.symm)
    · exact Or.inr <| Or.inr (by simpa [a2] using hyn.symm)
  have hcover_d {y : V} (hy : y ∈ d.supp) : y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 := by
    have hysupp : y ∈ q.support := by
      have hyverts : y ∈ q.toSubgraph.verts := hqverts.symm ▸ hy
      exact q.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn4 : n ≤ 4 := by simpa [hlenq] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [b0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [b1] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [b2] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr (by simpa [b3] using hyn.symm)
    · exact Or.inl <| by
        calc
          y = q.getVert 4 := hyn.symm
          _ = q.getVert q.length := by simpa [hlenq]
          _ = q.getVert 0 := by rw [q.getVert_length, q.getVert_zero]
          _ = b0 := rfl
  have hcover :
      ∀ y : V, y = a0 ∨ y = a1 ∨ y = a2 ∨ y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · rcases hcover_c hyc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
    · rcases hcover_d hyd with rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  let color : V → Fin 4 := fun y =>
    if y = a0 ∨ y = a1 then 0
    else if y = a2 then 1
    else if y = b0 ∨ y = b1 then 2
    else 3
  have hcolor_a0 : color a0 = 0 := by simp [color]
  have hcolor_a1 : color a1 = 0 := by simp [color]
  have hcolor_a2 : color a2 = 1 := by simp [color, ha20, ha21]
  have hcolor_b0 : color b0 = 2 := by
    simp [color, hb0a0, hb0a1, hb0a2]
  have hcolor_b1 : color b1 = 2 := by
    simp [color, hb1a0, hb1a1, hb1a2]
  have hcolor_b2 : color b2 = 3 := by
    simp [color, hb2a0, hb2a1, hb2a2, hb20, hb21]
  have hcolor_b3 : color b3 = 3 := by
    simp [color, hb3a0, hb3a1, hb3a2, hb30, hb31]
  have bucket0 {y : V} (hy : color y = 0) : y = a0 ∨ y = a1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
  have bucket1 {y : V} (hy : color y = 1) : y = a2 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · rfl
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y = b0 ∨ y = b1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
  have bucket3 {y : V} (hy : color y = 3) : y = b2 ∨ y = b3 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      rcases bucket0 hy0 with hya0 | hya1
      · subst y
        rcases bucket0 hz0 with hza0 | hza1
        · subst z
          exact (G.ne_of_adj hyz) rfl
        · subst z
          exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
      · subst y
        rcases bucket0 hz0 with hza0 | hza1
        · subst z
          exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
        · subst z
          exact (G.ne_of_adj hyz) rfl
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rw [bucket1 hy1, bucket1 hz1] at hyz
        exact G.loopless a2 hyz
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with hyb0 | hyb1
          · subst y
            rcases bucket2 hz2 with hzb0 | hzb1
            · subst z
              exact (G.ne_of_adj hyz) rfl
            · subst z
              exact ((SimpleGraph.compl_adj G b0 b1).1 hb01).2 hyz
          · subst y
            rcases bucket2 hz2 with hzb0 | hzb1
            · subst z
              exact ((SimpleGraph.compl_adj G b1 b0).1 hb01.symm).2 hyz
            · subst z
              exact (G.ne_of_adj hyz) rfl
        · have hy3 : color y = 3 := by
            rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact False.elim (hy0 hcolor_a0)
            · exact False.elim (hy0 hcolor_a1)
            · exact False.elim (hy1 hcolor_a2)
            · exact False.elim (hy2 hcolor_b0)
            · exact False.elim (hy2 hcolor_b1)
            · exact hcolor_b2
            · exact hcolor_b3
          have hz3 : color z = 3 := by rw [← hyzEq, hy3]
          rcases bucket3 hy3 with hyb2 | hyb3
          · subst y
            rcases bucket3 hz3 with hzb2 | hzb3
            · subst z
              exact (G.ne_of_adj hyz) rfl
            · subst z
              exact ((SimpleGraph.compl_adj G b2 b3).1 hb23).2 hyz
          · subst y
            rcases bucket3 hz3 with hzb2 | hzb3
            · subst z
              exact ((SimpleGraph.compl_adj G b3 b2).1 hb23.symm).2 hyz
            · subst z
              exact (G.ne_of_adj hyz) rfl
  exact hcolor.colorable

/-- If the complement splits as a `2`-vertex path component and a `5`-vertex cycle component,
then the original graph is `4`-colorable.

Source: new theorem closing the `P₂ ⊔ C₅` branch of the remaining seven-vertex `15`-edge
endpoint case. The path contributes one adjacent pair, and the `5`-cycle is colored by two
adjacent pairs plus one singleton. -/
theorem colorable_four_of_compl_path_component_card_two_and_cycle_component_card_five
    (hcard : Fintype.card V = 7)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp)
    {d : (Gᶜ).ConnectedComponent} (hcd : d ≠ (Gᶜ).connectedComponentMk u)
    (hd5 : d.supp.ncard = 5)
    (hunion : ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ)
    {x : V} {q : (Gᶜ).Walk x x} (hq : q.IsCycle) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  let c : (Gᶜ).ConnectedComponent := (Gᶜ).connectedComponentMk u
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ))
      (by simpa [c] using hcd.symm)
  have hc2 : c.supp.ncard = 2 := by
    have hsum : c.supp.ncard + d.supp.ncard = 7 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj]
        _ = 7 := by
          rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    omega
  have hlenp : p.length = 1 := by
    simpa [hpverts, c, hc2] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 5 := by
    simpa [hd5] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  let b3 : V := q.getVert 3
  let b4 : V := q.getVert 4
  have hgetq_ne :
      ∀ {m n : ℕ}, m ≤ 4 → n ≤ 4 → m ≠ n → q.getVert m ≠ q.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ q.length - 1 := by omega
    have hn' : n ≤ q.length - 1 := by omega
    apply hmn
    exact hq.getVert_injOn' hm' hn' hEq
  have hb20 : b2 ≠ b0 := by
    simpa [b2, b0] using hgetq_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have hb21 : b2 ≠ b1 := by
    simpa [b2, b1] using hgetq_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have hb30 : b3 ≠ b0 := by
    simpa [b3, b0] using hgetq_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have hb31 : b3 ≠ b1 := by
    simpa [b3, b1] using hgetq_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have hb40 : b4 ≠ b0 := by
    simpa [b4, b0] using hgetq_ne (m := 4) (n := 0) (by decide) (by decide) (by decide)
  have hb41 : b4 ≠ b1 := by
    simpa [b4, b1] using hgetq_ne (m := 4) (n := 1) (by decide) (by decide) (by decide)
  have hb42 : b4 ≠ b2 := by
    simpa [b4, b2] using hgetq_ne (m := 4) (n := 2) (by decide) (by decide) (by decide)
  have hb43 : b4 ≠ b3 := by
    simpa [b4, b3] using hgetq_ne (m := 4) (n := 3) (by decide) (by decide) (by decide)
  have ha01 : (Gᶜ).Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have hb01 : (Gᶜ).Adj b0 b1 := by
    have h0 : 0 < q.length := by omega
    simpa [b0, b1] using q.adj_getVert_succ h0
  have hb23 : (Gᶜ).Adj b2 b3 := by
    have h2 : 2 < q.length := by omega
    simpa [b2, b3] using q.adj_getVert_succ h2
  have ha0mem : a0 ∈ c.supp := by
    have : a0 ∈ p.toSubgraph.verts := by simpa [a0] using p.start_mem_verts_toSubgraph
    exact hpverts ▸ this
  have ha1mem : a1 ∈ c.supp := by
    have hsupp : a1 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [a1], by omega⟩
    have : a1 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp
    exact hpverts ▸ this
  have hb0mem : b0 ∈ d.supp := by
    have : b0 ∈ q.toSubgraph.verts := by simpa [b0] using q.start_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hb1mem : b1 ∈ d.supp := by
    have hsupp : b1 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [b1], by omega⟩
    have : b1 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb2mem : b2 ∈ d.supp := by
    have hsupp : b2 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [b2], by omega⟩
    have : b2 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb3mem : b3 ∈ d.supp := by
    have hsupp : b3 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [b3], by omega⟩
    have : b3 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb4mem : b4 ∈ d.supp := by
    have hsupp : b4 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨4, by simp [b4], by omega⟩
    have : b4 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp
    exact hqverts ▸ this
  have hb0notc : b0 ∉ c.supp := Set.disjoint_right.mp hdisj hb0mem
  have hb1notc : b1 ∉ c.supp := Set.disjoint_right.mp hdisj hb1mem
  have hb2notc : b2 ∉ c.supp := Set.disjoint_right.mp hdisj hb2mem
  have hb3notc : b3 ∉ c.supp := Set.disjoint_right.mp hdisj hb3mem
  have hb4notc : b4 ∉ c.supp := Set.disjoint_right.mp hdisj hb4mem
  have hb0a0 : b0 ≠ a0 := by intro hEq; exact hb0notc (hEq.symm ▸ ha0mem)
  have hb0a1 : b0 ≠ a1 := by intro hEq; exact hb0notc (hEq.symm ▸ ha1mem)
  have hb1a0 : b1 ≠ a0 := by intro hEq; exact hb1notc (hEq.symm ▸ ha0mem)
  have hb1a1 : b1 ≠ a1 := by intro hEq; exact hb1notc (hEq.symm ▸ ha1mem)
  have hb2a0 : b2 ≠ a0 := by intro hEq; exact hb2notc (hEq.symm ▸ ha0mem)
  have hb2a1 : b2 ≠ a1 := by intro hEq; exact hb2notc (hEq.symm ▸ ha1mem)
  have hb3a0 : b3 ≠ a0 := by intro hEq; exact hb3notc (hEq.symm ▸ ha0mem)
  have hb3a1 : b3 ≠ a1 := by intro hEq; exact hb3notc (hEq.symm ▸ ha1mem)
  have hb4a0 : b4 ≠ a0 := by intro hEq; exact hb4notc (hEq.symm ▸ ha0mem)
  have hb4a1 : b4 ≠ a1 := by intro hEq; exact hb4notc (hEq.symm ▸ ha1mem)
  have hcover_c {y : V} (hy : y ∈ c.supp) : y = a0 ∨ y = a1 := by
    have hysupp : y ∈ p.support := by
      have hyverts : y ∈ p.toSubgraph.verts := hpverts.symm ▸ hy
      exact p.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn1 : n ≤ 1 := by simpa [hlenp] using hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inl (by simpa [a0] using hyn.symm)
    · exact Or.inr (by simpa [a1] using hyn.symm)
  have hcover_d {y : V} (hy : y ∈ d.supp) : y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 ∨ y = b4 := by
    have hysupp : y ∈ q.support := by
      have hyverts : y ∈ q.toSubgraph.verts := hqverts.symm ▸ hy
      exact q.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hn⟩
    have hn5 : n ≤ 5 := by simpa [hlenq] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [b0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [b1] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [b2] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [b3] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (by simpa [b4] using hyn.symm)
    · exact Or.inl <| by
        calc
          y = q.getVert 5 := hyn.symm
          _ = q.getVert q.length := by simpa [hlenq]
          _ = q.getVert 0 := by rw [q.getVert_length, q.getVert_zero]
          _ = b0 := rfl
  have hcover :
      ∀ y : V, y = a0 ∨ y = a1 ∨ y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 ∨ y = b4 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · rcases hcover_c hyc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr <| Or.inl rfl
    · rcases hcover_d hyd with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  let color : V → Fin 4 := fun y =>
    if y = a0 ∨ y = a1 then 0
    else if y = b0 ∨ y = b1 then 1
    else if y = b2 ∨ y = b3 then 2
    else 3
  have hcolor_a0 : color a0 = 0 := by simp [color]
  have hcolor_a1 : color a1 = 0 := by simp [color]
  have hcolor_b0 : color b0 = 1 := by simp [color, hb0a0, hb0a1]
  have hcolor_b1 : color b1 = 1 := by simp [color, hb1a0, hb1a1]
  have hcolor_b2 : color b2 = 2 := by simp [color, hb2a0, hb2a1, hb20, hb21]
  have hcolor_b3 : color b3 = 2 := by simp [color, hb3a0, hb3a1, hb30, hb31]
  have hcolor_b4 : color b4 = 3 := by
    simp [color, hb4a0, hb4a1, hb40, hb41, hb42, hb43]
  have bucket0 {y : V} (hy : color y = 0) : y = a0 ∨ y = a1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b4] using hy
      exact False.elim this
  have bucket1 {y : V} (hy : color y = 1) : y = b0 ∨ y = b1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b4] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y = b2 ∨ y = b3 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b4] using hy
      exact False.elim this
  have bucket3 {y : V} (hy : color y = 3) : y = b4 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
    · rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      rcases bucket0 hy0 with hya0 | hya1
      · subst y
        rcases bucket0 hz0 with hza0 | hza1
        · subst z
          exact (G.ne_of_adj hyz) rfl
        · subst z
          exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
      · subst y
        rcases bucket0 hz0 with hza0 | hza1
        · subst z
          exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
        · subst z
          exact (G.ne_of_adj hyz) rfl
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rcases bucket1 hy1 with hyb0 | hyb1
        · subst y
          rcases bucket1 hz1 with hzb0 | hzb1
          · subst z
            exact (G.ne_of_adj hyz) rfl
          · subst z
            exact ((SimpleGraph.compl_adj G b0 b1).1 hb01).2 hyz
        · subst y
          rcases bucket1 hz1 with hzb0 | hzb1
          · subst z
            exact ((SimpleGraph.compl_adj G b1 b0).1 hb01.symm).2 hyz
          · subst z
            exact (G.ne_of_adj hyz) rfl
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with hyb2 | hyb3
          · subst y
            rcases bucket2 hz2 with hzb2 | hzb3
            · subst z
              exact (G.ne_of_adj hyz) rfl
            · subst z
              exact ((SimpleGraph.compl_adj G b2 b3).1 hb23).2 hyz
          · subst y
            rcases bucket2 hz2 with hzb2 | hzb3
            · subst z
              exact ((SimpleGraph.compl_adj G b3 b2).1 hb23.symm).2 hyz
            · subst z
              exact (G.ne_of_adj hyz) rfl
        · have hy3 : color y = 3 := by
            rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact False.elim (hy0 hcolor_a0)
            · exact False.elim (hy0 hcolor_a1)
            · exact False.elim (hy1 hcolor_b0)
            · exact False.elim (hy1 hcolor_b1)
            · exact False.elim (hy2 hcolor_b2)
            · exact False.elim (hy2 hcolor_b3)
            · exact hcolor_b4
          have hz3 : color z = 3 := by rw [← hyzEq, hy3]
          rw [bucket3 hy3, bucket3 hz3] at hyz
          exact G.loopless b4 hyz
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The remaining seven-vertex `15`-edge endpoint branch is explicitly `4`-colorable.

Source: new theorem combining the connected-branch exclusion with the three disconnected
path-plus-cycle colorings `P₄ ⊔ C₃`, `P₃ ⊔ C₄`, and `P₂ ⊔ C₅`. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    G.Colorable 4 := by
  rcases h.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      hcard hedge with
    ⟨u, v, _, p, hp, hpverts, d, hcd, hdcard, hunion, x, q, hq, hqverts⟩
  rcases hdcard with hd3 | hd4 | hd5
  · exact colorable_four_of_compl_path_component_card_four_and_cycle_component_card_three
      (G := G) hcard hp hpverts hcd hd3 hunion hq hqverts
  · exact colorable_four_of_compl_path_component_card_three_and_cycle_component_card_four
      (G := G) hcard hp hpverts hcd hd4 hunion hq hqverts
  · exact colorable_four_of_compl_path_component_card_two_and_cycle_component_card_five
      (G := G) hcard hp hpverts hcd hd5 hunion hq hqverts

/-- The seven-vertex `|E| = 15` case is impossible for incidence-critical non-4-colorable graphs.

Source: new theorem closing the last unresolved seven-vertex `15`-edge branch. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ne_fifteen_of_card_eq_seven
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 15 := by
  intro hedge
  exact h.not_colorable
    (h.colorable_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen hcard hedge)

/-- On seven vertices, a `K₅`-free incidence-critical non-4-colorable graph has at least `16`
edges.

Source: new sharpening of the previous `[15, 17]` window using the exclusion of the `|E| = 15`
branch. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card := by
  have h15 : 15 ≤ G.edgeFinset.card :=
    h.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree hcard hfree
  have hne15 : G.edgeFinset.card ≠ 15 :=
    h.card_edgeFinset_ne_fifteen_of_card_eq_seven hcard
  have hgt15 : 15 < G.edgeFinset.card :=
    lt_of_le_of_ne h15 (by simpa [eq_comm] using hne15)
  exact Nat.succ_le_of_lt hgt15

/-- On seven vertices, a `K₅`-free incidence-critical non-4-colorable graph has edge count in the
sharpened interval `[16, 17]`.

Source: new theorem combining the exclusion of `|E| = 15` with the previous `|E| ≤ 17`
exclusion. -/
theorem IsIncidenceCriticalNonColorable.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 := by
  exact ⟨h.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree,
    h.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `|E| = 15` exclusion. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ne_fifteen_of_card_eq_seven
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 15 :=
  (h.toIncidenceCritical_four).card_edgeFinset_ne_fifteen_of_card_eq_seven hcard

/-- Vertex-critical lift of the sharpened seven-vertex `16`-edge lower bound. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card :=
  h.toIncidenceCritical_four.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Vertex-critical lift of the sharpened seven-vertex edge window `[16, 17]`. -/
theorem IsVertexCriticalNonColorable.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 :=
  h.toIncidenceCritical_four.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `|E| = 15` exclusion. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_fifteen_of_card_eq_seven_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 15 :=
  ((h.toIncidenceCritical hadj)).card_edgeFinset_ne_fifteen_of_card_eq_seven hcard

/-- Minimal-counterexample lift of the sharpened seven-vertex `16`-edge lower bound. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift of the sharpened seven-vertex edge window `[16, 17]`. -/
theorem IsMinimalNonColorable.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 :=
  (h.toIncidenceCritical hadj).sharp_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
