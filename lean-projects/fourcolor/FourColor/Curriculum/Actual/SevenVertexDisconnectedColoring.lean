import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexConnectedColoring

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A cycle whose associated subgraph has vertex set `s` has length `s.ncard`.

Source: new helper theorem needed to turn cycle realizations of finite connected components into
exact small-cardinality cases. -/
theorem SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq
    {s : Set V} {v : V} {p : G.Walk v v} (hp : p.IsCycle) (hverts : p.toSubgraph.verts = s) :
    p.length = s.ncard := by
  letI : Fintype s := (Set.toFinite s).fintype
  let f : Fin p.length → s := fun i => ⟨p.getVert i, by
    have hxsupp : p.getVert i ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨i, rfl, le_of_lt i.is_lt⟩
    have hxverts : p.getVert i ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hxsupp
    rw [← hverts]
    exact hxverts⟩
  have hlen_le' : p.length ≤ Fintype.card s := by
    simpa using Fintype.card_le_of_injective f (by
      intro i j hij
      have hi : (i : ℕ) ≤ p.length - 1 := by omega
      have hj : (j : ℕ) ≤ p.length - 1 := by omega
      apply Fin.ext
      exact hp.getVert_injOn' hi hj (congrArg Subtype.val hij))
  have hlen_ge' : Fintype.card s ≤ p.length := by
    simpa using Fintype.card_le_of_surjective f (by
      intro x
      have hxverts : (x : V) ∈ p.toSubgraph.verts := by
        rw [hverts]
        exact x.property
      have hxsupp : (x : V) ∈ p.support := p.mem_verts_toSubgraph.mp hxverts
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
      by_cases hnp : n = p.length
      · have h0lt : 0 < p.length := by
          have := hp.three_le_length
          omega
        refine ⟨⟨0, h0lt⟩, ?_⟩
        apply Subtype.ext
        change p.getVert 0 = x
        calc
          p.getVert 0 = p.getVert p.length := by rw [p.getVert_zero, p.getVert_length]
          _ = x := by simpa [hnp] using hxn
      · have hnlt : n < p.length := by omega
        refine ⟨⟨n, hnlt⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using hxn)
  have hs_card : Fintype.card s = s.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hlen_le : p.length ≤ s.ncard := by simpa [hs_card] using hlen_le'
  have hlen_ge : s.ncard ≤ p.length := by simpa [hs_card] using hlen_ge'
  exact Nat.le_antisymm hlen_le hlen_ge

/-- If the complement splits into connected cycle-components of sizes `3` and `4`, then the
original graph is `4`-colorable.

Source: new theorem closing the disconnected branch of the sharp seven-vertex low-edge case by
coloring the 3-component uniformly and the 4-component by pairing adjacent vertices along the
complement cycle. -/
theorem colorable_four_of_compl_cycle_components_card_three_four
    {c d : (Gᶜ).ConnectedComponent} (hcd : c ≠ d)
    (hc3 : c.supp.ncard = 3) (hd4 : d.supp.ncard = 4)
    (hunion : c.supp ∪ d.supp = Set.univ)
    {vc vd : V} {pc : (Gᶜ).Walk vc vc} {pd : (Gᶜ).Walk vd vd}
    (hpc : pc.IsCycle) (hpcverts : pc.toSubgraph.verts = c.supp)
    (hpd : pd.IsCycle) (hpdverts : pd.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hcd
  have hlenc : pc.length = 3 := by
    simpa [hc3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hpc hpcverts)
  have hlend : pd.length = 4 := by
    simpa [hd4] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hpd hpdverts)
  let c0 : V := pc.getVert 0
  let c1 : V := pc.getVert 1
  let c2 : V := pc.getVert 2
  let d0 : V := pd.getVert 0
  let d1 : V := pd.getVert 1
  let d2 : V := pd.getVert 2
  let d3 : V := pd.getVert 3
  have hgetc_ne :
      ∀ {m n : ℕ}, m ≤ 2 → n ≤ 2 → m ≠ n → pc.getVert m ≠ pc.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ pc.length - 1 := by omega
    have hn' : n ≤ pc.length - 1 := by omega
    apply hmn
    exact hpc.getVert_injOn' hm' hn' hEq
  have hgetd_ne :
      ∀ {m n : ℕ}, m ≤ 3 → n ≤ 3 → m ≠ n → pd.getVert m ≠ pd.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ pd.length - 1 := by omega
    have hn' : n ≤ pd.length - 1 := by omega
    apply hmn
    exact hpd.getVert_injOn' hm' hn' hEq
  have hd20 : d2 ≠ d0 := by
    simpa [d2, d0] using hgetd_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have hd21 : d2 ≠ d1 := by
    simpa [d2, d1] using hgetd_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have hd30 : d3 ≠ d0 := by
    simpa [d3, d0] using hgetd_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have hd31 : d3 ≠ d1 := by
    simpa [d3, d1] using hgetd_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have hc01 : Gᶜ.Adj c0 c1 := by
    have h0 : 0 < pc.length := by omega
    simpa [c0, c1] using pc.adj_getVert_succ h0
  have hc12 : Gᶜ.Adj c1 c2 := by
    have h1 : 1 < pc.length := by omega
    simpa [c1, c2] using pc.adj_getVert_succ h1
  have hc20 : Gᶜ.Adj c2 c0 := by
    have h2 : 2 < pc.length := by omega
    have h20' : Gᶜ.Adj (pc.getVert 2) (pc.getVert pc.length) := by
      simpa [hlenc] using pc.adj_getVert_succ h2
    simpa [c2, c0, pc.getVert_zero, pc.getVert_length] using h20'
  have hd01 : Gᶜ.Adj d0 d1 := by
    have h0 : 0 < pd.length := by omega
    simpa [d0, d1] using pd.adj_getVert_succ h0
  have hd23 : Gᶜ.Adj d2 d3 := by
    have h2 : 2 < pd.length := by omega
    simpa [d2, d3] using pd.adj_getVert_succ h2
  have hd0mem : d0 ∈ d.supp := by
    have : d0 ∈ pd.toSubgraph.verts := by
      simpa [d0] using pd.start_mem_verts_toSubgraph
    exact hpdverts ▸ this
  have hd1mem : d1 ∈ d.supp := by
    have hsupp : d1 ∈ pd.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [d1], by omega⟩
    have : d1 ∈ pd.toSubgraph.verts := pd.mem_verts_toSubgraph.mpr hsupp
    exact hpdverts ▸ this
  have hd2mem : d2 ∈ d.supp := by
    have hsupp : d2 ∈ pd.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [d2], by omega⟩
    have : d2 ∈ pd.toSubgraph.verts := pd.mem_verts_toSubgraph.mpr hsupp
    exact hpdverts ▸ this
  have hd3mem : d3 ∈ d.supp := by
    have hsupp : d3 ∈ pd.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [d3], by omega⟩
    have : d3 ∈ pd.toSubgraph.verts := pd.mem_verts_toSubgraph.mpr hsupp
    exact hpdverts ▸ this
  have hd0notc : d0 ∉ c.supp := Set.disjoint_right.mp hdisj hd0mem
  have hd1notc : d1 ∉ c.supp := Set.disjoint_right.mp hdisj hd1mem
  have hd2notc : d2 ∉ c.supp := Set.disjoint_right.mp hdisj hd2mem
  have hd3notc : d3 ∉ c.supp := Set.disjoint_right.mp hdisj hd3mem
  have hcover_c {x : V} (hx : x ∈ c.supp) : x = c0 ∨ x = c1 ∨ x = c2 := by
    have hxsupp : x ∈ pc.support := by
      have hxverts : x ∈ pc.toSubgraph.verts := hpcverts.symm ▸ hx
      exact pc.mem_verts_toSubgraph.mp hxverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlenc] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [c0] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [c1] using hxn.symm)
    · exact Or.inr <| Or.inr (by simpa [c2] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = pc.getVert 3 := hxn.symm
          _ = pc.getVert pc.length := by simpa [hlenc]
          _ = pc.getVert 0 := by rw [pc.getVert_length, pc.getVert_zero]
          _ = c0 := rfl
  have hcover_d {x : V} (hx : x ∈ d.supp) : x = d0 ∨ x = d1 ∨ x = d2 ∨ x = d3 := by
    have hxsupp : x ∈ pd.support := by
      have hxverts : x ∈ pd.toSubgraph.verts := hpdverts.symm ▸ hx
      exact pd.mem_verts_toSubgraph.mp hxverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn4 : n ≤ 4 := by simpa [hlend] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [d0] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [d1] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [d2] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr (by simpa [d3] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = pd.getVert 4 := hxn.symm
          _ = pd.getVert pd.length := by simpa [hlend]
          _ = pd.getVert 0 := by rw [pd.getVert_length, pd.getVert_zero]
          _ = d0 := rfl
  have hcover :
      ∀ x : V, x ∈ c.supp ∨ x = d0 ∨ x = d1 ∨ x = d2 ∨ x = d3 := by
    intro x
    have hxunion : x ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hxunion with hxc | hxd
    · exact Or.inl hxc
    · rcases hcover_d hxd with rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  have htri {x y : V} (hx : x ∈ c.supp) (hy : y ∈ c.supp) (hxy : x ≠ y) : Gᶜ.Adj x y := by
    rcases hcover_c hx with rfl | rfl | rfl
    · rcases hcover_c hy with rfl | rfl | rfl
      · exact False.elim (hxy rfl)
      · exact hc01
      · exact hc20.symm
    · rcases hcover_c hy with rfl | rfl | rfl
      · exact hc01.symm
      · exact False.elim (hxy rfl)
      · exact hc12
    · rcases hcover_c hy with rfl | rfl | rfl
      · exact hc20
      · exact hc12.symm
      · exact False.elim (hxy rfl)
  let color : V → Fin 4 := fun x =>
    if x ∈ c.supp then 0
    else if x = d0 ∨ x = d1 then 1
    else if x = d2 ∨ x = d3 then 2
    else 3
  have hcolor_c {x : V} (hx : x ∈ c.supp) : color x = 0 := by
    change (if x ∈ c.supp then 0 else if x = d0 ∨ x = d1 then 1 else if x = d2 ∨ x = d3 then 2 else 3) = 0
    rw [if_pos hx]
  have hcolor_d0 : color d0 = 1 := by
    change (if d0 ∈ c.supp then 0 else if d0 = d0 ∨ d0 = d1 then 1 else if d0 = d2 ∨ d0 = d3 then 2 else 3) = 1
    rw [if_neg hd0notc, if_pos (Or.inl rfl)]
  have hcolor_d1 : color d1 = 1 := by
    change (if d1 ∈ c.supp then 0 else if d1 = d0 ∨ d1 = d1 then 1 else if d1 = d2 ∨ d1 = d3 then 2 else 3) = 1
    rw [if_neg hd1notc, if_pos (Or.inr rfl)]
  have hcolor_d2 : color d2 = 2 := by
    change (if d2 ∈ c.supp then 0 else if d2 = d0 ∨ d2 = d1 then 1 else if d2 = d2 ∨ d2 = d3 then 2 else 3) = 2
    rw [if_neg hd2notc, if_neg (by
      intro hd
      rcases hd with h | h
      · exact hd20 h
      · exact hd21 h), if_pos (Or.inl rfl)]
  have hcolor_d3 : color d3 = 2 := by
    change (if d3 ∈ c.supp then 0 else if d3 = d0 ∨ d3 = d1 then 1 else if d3 = d2 ∨ d3 = d3 then 2 else 3) = 2
    rw [if_neg hd3notc, if_neg (by
      intro hd
      rcases hd with h | h
      · exact hd30 h
      · exact hd31 h), if_pos (Or.inr rfl)]
  have bucket0 {x : V} (hx : color x = 0) : x ∈ c.supp := by
    by_cases hxc : x ∈ c.supp
    · exact hxc
    · rcases hcover x with hxc' | rfl | rfl | rfl | rfl
      · contradiction
      · have : False := by simpa [hcolor_d0] using hx
        exact False.elim this
      · have : False := by simpa [hcolor_d1] using hx
        exact False.elim this
      · have : False := by simpa [hcolor_d2] using hx
        exact False.elim this
      · have : False := by simpa [hcolor_d3] using hx
        exact False.elim this
  have bucket1 {x : V} (hx : color x = 1) : x = d0 ∨ x = d1 := by
    rcases hcover x with hxc | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_c hxc] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_d2] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_d3] using hx
      exact False.elim this
  have bucket2 {x : V} (hx : color x = 2) : x = d2 ∨ x = d3 := by
    rcases hcover x with hxc | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_c hxc] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_d0] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_d1] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    by_cases hxc : x ∈ c.supp
    · have hcx : color x = 0 := hcolor_c hxc
      have hcy : color y = 0 := by rw [← hEq, hcx]
      have hyc : y ∈ c.supp := bucket0 hcy
      by_cases hxy' : x = y
      · exact (G.ne_of_adj hxy) hxy'
      · exact ((SimpleGraph.compl_adj G x y).1 (htri hxc hyc hxy')).2 hxy
    · by_cases hxd01 : x = d0 ∨ x = d1
      · have hcx : color x = 1 := by
          change (if x ∈ c.supp then 0 else if x = d0 ∨ x = d1 then 1 else if x = d2 ∨ x = d3 then 2 else 3) = 1
          rw [if_neg hxc, if_pos hxd01]
        have hcy : color y = 1 := by rw [← hEq, hcx]
        rcases hxd01 with rfl | rfl
        · rcases bucket1 hcy with rfl | rfl
          · exact (G.ne_of_adj hxy) rfl
          · exact ((SimpleGraph.compl_adj G d0 d1).1 hd01).2 hxy
        · rcases bucket1 hcy with rfl | rfl
          · exact ((SimpleGraph.compl_adj G d1 d0).1 hd01.symm).2 hxy
          · exact (G.ne_of_adj hxy) rfl
      · by_cases hxd23 : x = d2 ∨ x = d3
        · have hcx : color x = 2 := by
            change (if x ∈ c.supp then 0 else if x = d0 ∨ x = d1 then 1 else if x = d2 ∨ x = d3 then 2 else 3) = 2
            rw [if_neg hxc, if_neg hxd01, if_pos hxd23]
          have hcy : color y = 2 := by rw [← hEq, hcx]
          rcases hxd23 with rfl | rfl
          · rcases bucket2 hcy with rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact ((SimpleGraph.compl_adj G d2 d3).1 hd23).2 hxy
          · rcases bucket2 hcy with rfl | rfl
            · exact ((SimpleGraph.compl_adj G d3 d2).1 hd23.symm).2 hxy
            · exact (G.ne_of_adj hxy) rfl
        · have hcx : color x = 3 := by
            change (if x ∈ c.supp then 0 else if x = d0 ∨ x = d1 then 1 else if x = d2 ∨ x = d3 then 2 else 3) = 3
            rw [if_neg hxc, if_neg hxd01, if_neg hxd23]
          have : False := by
            rcases hcover x with hxmem | rfl | rfl | rfl | rfl
            · simpa [hcolor_c hxmem] using hcx
            · simpa [hcolor_d0] using hcx
            · simpa [hcolor_d1] using hcx
            · simpa [hcolor_d2] using hcx
            · simpa [hcolor_d3] using hcx
          exact False.elim this
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the disconnected branch of the sharp seven-vertex low-edge case, the original graph is
`4`-colorable.

Source: new theorem combining the `3+4` complement-component realization with explicit componentwise
coloring data. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14)
    (hnot : ¬ Gᶜ.Connected) :
    G.Colorable 4 := by
  rcases h.compl_exists_distinct_components_card_three_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
      hcard hedge hnot with ⟨c, d, hcd, hc3, hd4⟩
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hcd
  have hunion7 : (c.supp ∪ d.supp).ncard = 7 := by
    rw [Set.ncard_union_eq hdisj]
    simp [hc3, hd4]
  have hunion : c.supp ∪ d.supp = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite Set.univ)
    · intro x hx
      simp
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hunion7]
  have hreg : Gᶜ.IsRegularOfDegree 2 :=
    h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge
  have hcyc : Gᶜ.IsCycles := isCycles_of_isRegularOfDegree_two hreg
  let vc : V := c.nonempty_supp.some
  let vd : V := d.nonempty_supp.some
  have hvc : vc ∈ c.supp := c.nonempty_supp.some_mem
  have hvd : vd ∈ d.supp := d.nonempty_supp.some_mem
  have hneighc : ((Gᶜ).neighborSet vc).Nonempty := by
    have hdeg : (Gᶜ).degree vc = 2 := hreg vc
    have hdeg_pos : 0 < (Gᶜ).degree vc := by simp [hdeg]
    rcases ((Gᶜ).degree_pos_iff_exists_adj vc).1 hdeg_pos with ⟨w, hw⟩
    exact ⟨w, hw⟩
  have hneighd : ((Gᶜ).neighborSet vd).Nonempty := by
    have hdeg : (Gᶜ).degree vd = 2 := hreg vd
    have hdeg_pos : 0 < (Gᶜ).degree vd := by simp [hdeg]
    rcases ((Gᶜ).degree_pos_iff_exists_adj vd).1 hdeg_pos with ⟨w, hw⟩
    exact ⟨w, hw⟩
  rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := c) hvc hneighc with
    ⟨pc, hpc, hpcverts⟩
  rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := d) hvd hneighd with
    ⟨pd, hpd, hpdverts⟩
  exact colorable_four_of_compl_cycle_components_card_three_four
    (G := G) hcd hc3 hd4 hunion hpc hpcverts hpd hpdverts

/-- The sharp seven-vertex low-edge case `|E| = 14` is impossible for incidence-critical
non-4-colorable graphs.

Source: new theorem combining the connected-branch exclusion with the disconnected-branch explicit
coloring. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_seven
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 14 := by
  intro hedge
  have hnot : ¬ Gᶜ.Connected :=
    h.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge
  exact h.not_colorable
    (h.colorable_four_of_not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
      hcard hedge hnot)

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `|E| = 14` exclusion. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_seven
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 14 :=
  (h.toIncidenceCritical_four).card_edgeFinset_ne_fourteen_of_card_eq_seven hcard

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `|E| = 14` exclusion. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_seven_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) :
    G.edgeFinset.card ≠ 14 :=
  ((h.toIncidenceCritical hadj)).card_edgeFinset_ne_fourteen_of_card_eq_seven hcard

/-- Minimal-counterexample lift of the seven-vertex `|E| = 14` exclusion under `K₅`-freeness
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 14 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.card_edgeFinset_ne_fourteen_of_card_eq_seven hcard

end MinimalBridge

end FourColor.Curriculum.Actual
