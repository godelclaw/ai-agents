import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexFifteenSupportCases
import FourColor.Curriculum.Actual.SevenVertexRealization
import FourColor.Curriculum.Actual.SevenVertexConnectedColoring
import FourColor.Curriculum.Actual.SevenVertexDisconnectedColoring

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the isolated-support half of the seven-vertex `15`-edge branch, the complement support is
the complement of the isolated vertex. -/
theorem compl_support_eq_compl_singleton_of_card_eq_seven_of_compl_degree_eq_zero_of_card_support_eq_six
    (hcard : Fintype.card V = 7) {u : V} (hu0 : Gᶜ.degree u = 0)
    (hsupp : Fintype.card Gᶜ.support = 6) :
    Gᶜ.support = ({u} : Set V)ᶜ := by
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite (({u} : Set V)ᶜ))
  · intro w hw
    have hwu : w ≠ u := by
      intro hEq
      exact hu_not_mem (hEq ▸ hw)
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hwu
  · have hsupp_ncard : Gᶜ.support.ncard = 6 := by
      have hs_card : Fintype.card ↥(Gᶜ.support) = Gᶜ.support.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simpa [hs_card] using hsupp
    have hcomp_card : Fintype.card ↥((({u} : Set V)ᶜ)) = 6 := by
      have hcomp_eq :
          Fintype.card ↥((({u} : Set V)ᶜ)) = Fintype.card V - Fintype.card ↥({u} : Set V) := by
        simpa using (Fintype.card_compl_set ({u} : Set V))
      calc
        Fintype.card ↥((({u} : Set V)ᶜ)) = Fintype.card V - Fintype.card ↥({u} : Set V) := hcomp_eq
        _ = 7 - 1 := by rw [hcard]; simp
        _ = 6 := by decide
    have hcomp_ncard : (({u} : Set V)ᶜ).ncard = 6 := by
      have hcomp_card' : Fintype.card ↥((({u} : Set V)ᶜ)) = (({u} : Set V)ᶜ).ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simpa [hcomp_card'] using hcomp_card
    omega

/-- If the complement has one isolated vertex and the remaining six support vertices form a single
cycle, then the original seven-vertex graph is `4`-colorable. -/
theorem colorable_four_of_isolated_compl_vertex_and_compl_support_cycle_covering_all_vertices
    (hcard : Fintype.card V = 7) {u : V} (hu0 : Gᶜ.degree u = 0)
    (hsupp : Fintype.card Gᶜ.support = 6)
    {v : Gᶜ.support} {p : ((Gᶜ).induce (Gᶜ.support)).Walk v v}
    (hp : p.IsCycle) (hverts : p.toSubgraph.verts = Set.univ) :
    G.Colorable 4 := by
  classical
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
  have hsupport :
      Gᶜ.support = ({u} : Set V)ᶜ :=
    compl_support_eq_compl_singleton_of_card_eq_seven_of_compl_degree_eq_zero_of_card_support_eq_six
      (G := G) hcard hu0 hsupp
  have hlen : p.length = 6 := by
    simpa [H, hsupp] using
      (SimpleGraph.Walk.IsCycle.length_eq_card_of_toSubgraph_verts_eq_univ
        (G := H) hp hverts)
  let a0s : Gᶜ.support := p.getVert 0
  let a1s : Gᶜ.support := p.getVert 1
  let a2s : Gᶜ.support := p.getVert 2
  let a3s : Gᶜ.support := p.getVert 3
  let a4s : Gᶜ.support := p.getVert 4
  let a5s : Gᶜ.support := p.getVert 5
  let a0 : V := a0s
  let a1 : V := a1s
  let a2 : V := a2s
  let a3 : V := a3s
  let a4 : V := a4s
  let a5 : V := a5s
  have hget_ne :
      ∀ {m n : ℕ}, m ≤ 5 → n ≤ 5 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ p.length - 1 := by omega
    have hn' : n ≤ p.length - 1 := by omega
    apply hmn
    exact hp.getVert_injOn' hm' hn' hEq
  have h20s : a2s ≠ a0s := by
    simpa [a2s, a0s] using hget_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have h21s : a2s ≠ a1s := by
    simpa [a2s, a1s] using hget_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have h30s : a3s ≠ a0s := by
    simpa [a3s, a0s] using hget_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have h31s : a3s ≠ a1s := by
    simpa [a3s, a1s] using hget_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have h40s : a4s ≠ a0s := by
    simpa [a4s, a0s] using hget_ne (m := 4) (n := 0) (by decide) (by decide) (by decide)
  have h41s : a4s ≠ a1s := by
    simpa [a4s, a1s] using hget_ne (m := 4) (n := 1) (by decide) (by decide) (by decide)
  have h42s : a4s ≠ a2s := by
    simpa [a4s, a2s] using hget_ne (m := 4) (n := 2) (by decide) (by decide) (by decide)
  have h43s : a4s ≠ a3s := by
    simpa [a4s, a3s] using hget_ne (m := 4) (n := 3) (by decide) (by decide) (by decide)
  have h50s : a5s ≠ a0s := by
    simpa [a5s, a0s] using hget_ne (m := 5) (n := 0) (by decide) (by decide) (by decide)
  have h51s : a5s ≠ a1s := by
    simpa [a5s, a1s] using hget_ne (m := 5) (n := 1) (by decide) (by decide) (by decide)
  have h52s : a5s ≠ a2s := by
    simpa [a5s, a2s] using hget_ne (m := 5) (n := 2) (by decide) (by decide) (by decide)
  have h53s : a5s ≠ a3s := by
    simpa [a5s, a3s] using hget_ne (m := 5) (n := 3) (by decide) (by decide) (by decide)
  have h54s : a5s ≠ a4s := by
    simpa [a5s, a4s] using hget_ne (m := 5) (n := 4) (by decide) (by decide) (by decide)
  have h20 : a2 ≠ a0 := fun hEq => h20s (Subtype.ext hEq)
  have h21 : a2 ≠ a1 := fun hEq => h21s (Subtype.ext hEq)
  have h30 : a3 ≠ a0 := fun hEq => h30s (Subtype.ext hEq)
  have h31 : a3 ≠ a1 := fun hEq => h31s (Subtype.ext hEq)
  have h40 : a4 ≠ a0 := fun hEq => h40s (Subtype.ext hEq)
  have h41 : a4 ≠ a1 := fun hEq => h41s (Subtype.ext hEq)
  have h42 : a4 ≠ a2 := fun hEq => h42s (Subtype.ext hEq)
  have h43 : a4 ≠ a3 := fun hEq => h43s (Subtype.ext hEq)
  have h50 : a5 ≠ a0 := fun hEq => h50s (Subtype.ext hEq)
  have h51 : a5 ≠ a1 := fun hEq => h51s (Subtype.ext hEq)
  have h52 : a5 ≠ a2 := fun hEq => h52s (Subtype.ext hEq)
  have h53 : a5 ≠ a3 := fun hEq => h53s (Subtype.ext hEq)
  have h54 : a5 ≠ a4 := fun hEq => h54s (Subtype.ext hEq)
  have h01adj : Gᶜ.Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [H, a0s, a1s, a0, a1] using p.adj_getVert_succ h0
  have h23adj : Gᶜ.Adj a2 a3 := by
    have h2 : 2 < p.length := by omega
    simpa [H, a2s, a3s, a2, a3] using p.adj_getVert_succ h2
  have h45adj : Gᶜ.Adj a4 a5 := by
    have h4 : 4 < p.length := by omega
    simpa [H, a4s, a5s, a4, a5] using p.adj_getVert_succ h4
  have hcover_support :
      ∀ x : Gᶜ.support,
        x = a0s ∨ x = a1s ∨ x = a2s ∨ x = a3s ∨ x = a4s ∨ x = a5s := by
    intro x
    have hxsupp : x ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hverts]
      simp
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn6 : n ≤ 6 := by simpa [hlen] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [a0s] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1s] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [a2s] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a3s] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a4s] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (by simpa [a5s] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = p.getVert 6 := hxn.symm
          _ = p.getVert p.length := by simpa [hlen]
          _ = p.getVert 0 := by rw [p.getVert_length, p.getVert_zero]
          _ = a0s := rfl
  have hcover :
      ∀ x : V, x = u ∨ x = a0 ∨ x = a1 ∨ x = a2 ∨ x = a3 ∨ x = a4 ∨ x = a5 := by
    intro x
    by_cases hxu : x = u
    · exact Or.inl hxu
    · have hxcomp : x ∈ ({u} : Set V)ᶜ := by simp [hxu]
      have hxsupp : x ∈ Gᶜ.support := by simpa [hsupport] using hxcomp
      let xs : Gᶜ.support := ⟨x, hxsupp⟩
      rcases hcover_support xs with h0 | h1 | h2 | h3 | h4 | h5
      · exact Or.inr <| Or.inl (by exact congrArg Subtype.val h0)
      · exact Or.inr <| Or.inr <| Or.inl (by exact congrArg Subtype.val h1)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by exact congrArg Subtype.val h2)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by exact congrArg Subtype.val h3)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          (by exact congrArg Subtype.val h4)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
          (by exact congrArg Subtype.val h5)
  let color : V → Fin 4 := fun x =>
    if x = u then 3
    else if x = a0 ∨ x = a1 then 0
    else if x = a2 ∨ x = a3 then 1
    else 2
  have ha0u : a0 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a0, hEq] using a0s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have ha1u : a1 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a1, hEq] using a1s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have ha2u : a2 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a2, hEq] using a2s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have ha3u : a3 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a3, hEq] using a3s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have ha4u : a4 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a4, hEq] using a4s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have ha5u : a5 ≠ u := by
    intro hEq
    have : u ∈ Gᶜ.support := by simpa [a5, hEq] using a5s.property
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0 this
  have hcolor_u : color u = 3 := by simp [color]
  have hcolor_a0 : color a0 = 0 := by simp [color, ha0u]
  have hcolor_a1 : color a1 = 0 := by simp [color, ha1u]
  have hcolor_a2 : color a2 = 1 := by simp [color, ha2u, h20, h21]
  have hcolor_a3 : color a3 = 1 := by simp [color, ha3u, h30, h31]
  have hcolor_a4 : color a4 = 2 := by simp [color, ha4u, h40, h41, h42, h43]
  have hcolor_a5 : color a5 = 2 := by simp [color, ha5u, h50, h51, h52, h53, h54]
  have bucket0 {x : V} (hx : color x = 0) : x = a0 ∨ x = a1 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a2] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a4] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a5] using hx
      exact False.elim this
  have bucket1 {x : V} (hx : color x = 1) : x = a2 ∨ x = a3 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a0] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a4] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a5] using hx
      exact False.elim this
  have bucket2 {x : V} (hx : color x = 2) : x = a4 ∨ x = a5 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a0] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
  have bucket3 {x : V} (hx : color x = 3) : x = u := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · simpa [hcolor_a0] using hx
    · simpa [hcolor_a1] using hx
    · simpa [hcolor_a2] using hx
    · simpa [hcolor_a3] using hx
    · simpa [hcolor_a4] using hx
    · simpa [hcolor_a5] using hx
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    by_cases hxu : x = u
    · subst x
      have hcx : color u = 3 := hcolor_u
      have hcy : color y = 3 := by rw [← hEq, hcx]
      rw [bucket3 hcy] at hxy
      exact G.loopless u hxy
    · by_cases hx01 : x = a0 ∨ x = a1
      · have hcx : color x = 0 := by simp [color, hxu, hx01]
        have hcy : color y = 0 := by rw [← hEq, hcx]
        rcases hx01 with rfl | rfl
        · rcases bucket0 hcy with rfl | rfl
          · exact (G.ne_of_adj hxy) rfl
          · exact ((SimpleGraph.compl_adj G a0 a1).1 h01adj).2 hxy
        · rcases bucket0 hcy with rfl | rfl
          · exact ((SimpleGraph.compl_adj G a1 a0).1 h01adj.symm).2 hxy
          · exact (G.ne_of_adj hxy) rfl
      · by_cases hx23 : x = a2 ∨ x = a3
        · have hcx : color x = 1 := by simp [color, hxu, hx01, hx23]
          have hcy : color y = 1 := by rw [← hEq, hcx]
          rcases hx23 with rfl | rfl
          · rcases bucket1 hcy with rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact ((SimpleGraph.compl_adj G a2 a3).1 h23adj).2 hxy
          · rcases bucket1 hcy with rfl | rfl
            · exact ((SimpleGraph.compl_adj G a3 a2).1 h23adj.symm).2 hxy
            · exact (G.ne_of_adj hxy) rfl
        · have hcx : color x = 2 := by simp [color, hxu, hx01, hx23]
          have hcy : color y = 2 := by rw [← hEq, hcx]
          rcases bucket2 hcy with rfl | rfl
          · rcases bucket2 hcx with rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact ((SimpleGraph.compl_adj G a5 a4).1 h45adj.symm).2 hxy
          · rcases bucket2 hcx with rfl | rfl
            · exact ((SimpleGraph.compl_adj G a4 a5).1 h45adj).2 hxy
            · exact (G.ne_of_adj hxy) rfl
  exact hcolor.colorable

/-- If the complement has one isolated vertex and the remaining support splits as two
three-cycles, then the original seven-vertex graph is `4`-colorable. -/
theorem colorable_four_of_isolated_compl_vertex_and_compl_support_cycle_components_card_three_three
    (hcard : Fintype.card V = 7) {u : V} (hu0 : Gᶜ.degree u = 0)
    (hsupp : Fintype.card Gᶜ.support = 6)
    {c d : ((Gᶜ).induce (Gᶜ.support)).ConnectedComponent} (hcd : c ≠ d)
    (hc3 : c.supp.ncard = 3) (hd3 : d.supp.ncard = 3)
    {vc vd : Gᶜ.support}
    {pc : ((Gᶜ).induce (Gᶜ.support)).Walk vc vc}
    {pd : ((Gᶜ).induce (Gᶜ.support)).Walk vd vd}
    (hpc : pc.IsCycle) (hpcverts : pc.toSubgraph.verts = c.supp)
    (hpd : pd.IsCycle) (hpdverts : pd.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
  have hsupport :
      Gᶜ.support = ({u} : Set V)ᶜ :=
    compl_support_eq_compl_singleton_of_card_eq_seven_of_compl_degree_eq_zero_of_card_support_eq_six
      (G := G) hcard hu0 hsupp
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hcd
  have hlenc : pc.length = 3 := by
    simpa [hc3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := H) hpc hpcverts)
  have hlend : pd.length = 3 := by
    simpa [hd3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := H) hpd hpdverts)
  have hunion6 : (c.supp ∪ d.supp).ncard = 6 := by
    rw [Set.ncard_union_eq hdisj]
    simp [hc3, hd3]
  have hunion : c.supp ∪ d.supp = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite Set.univ)
    · intro x hx
      simp
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card, hsupp, hunion6]
  let c0s : Gᶜ.support := pc.getVert 0
  let c1s : Gᶜ.support := pc.getVert 1
  let c2s : Gᶜ.support := pc.getVert 2
  let d0s : Gᶜ.support := pd.getVert 0
  let d1s : Gᶜ.support := pd.getVert 1
  let d2s : Gᶜ.support := pd.getVert 2
  let c0 : V := c0s
  let c1 : V := c1s
  let c2 : V := c2s
  let d0 : V := d0s
  let d1 : V := d1s
  let d2 : V := d2s
  have hgetc_ne :
      ∀ {m n : ℕ}, m ≤ 2 → n ≤ 2 → m ≠ n → pc.getVert m ≠ pc.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ pc.length - 1 := by omega
    have hn' : n ≤ pc.length - 1 := by omega
    apply hmn
    exact hpc.getVert_injOn' hm' hn' hEq
  have hgetd_ne :
      ∀ {m n : ℕ}, m ≤ 2 → n ≤ 2 → m ≠ n → pd.getVert m ≠ pd.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ pd.length - 1 := by omega
    have hn' : n ≤ pd.length - 1 := by omega
    apply hmn
    exact hpd.getVert_injOn' hm' hn' hEq
  have hc01 : H.Adj c0s c1s := by
    have h0 : 0 < pc.length := by omega
    simpa [H, c0s, c1s] using pc.adj_getVert_succ h0
  have hc12 : H.Adj c1s c2s := by
    have h1 : 1 < pc.length := by omega
    simpa [H, c1s, c2s] using pc.adj_getVert_succ h1
  have hc20 : H.Adj c2s c0s := by
    have h2 : 2 < pc.length := by omega
    have h20' : H.Adj (pc.getVert 2) (pc.getVert pc.length) := by
      simpa [H, hlenc] using pc.adj_getVert_succ h2
    simpa [H, c2s, c0s, pc.getVert_zero, pc.getVert_length] using h20'
  have hd01 : H.Adj d0s d1s := by
    have h0 : 0 < pd.length := by omega
    simpa [H, d0s, d1s] using pd.adj_getVert_succ h0
  have hd12 : H.Adj d1s d2s := by
    have h1 : 1 < pd.length := by omega
    simpa [H, d1s, d2s] using pd.adj_getVert_succ h1
  have hd20 : H.Adj d2s d0s := by
    have h2 : 2 < pd.length := by omega
    have h20' : H.Adj (pd.getVert 2) (pd.getVert pd.length) := by
      simpa [H, hlend] using pd.adj_getVert_succ h2
    simpa [H, d2s, d0s, pd.getVert_zero, pd.getVert_length] using h20'
  have hcover_c {x : Gᶜ.support} (hx : x ∈ c.supp) : x = c0s ∨ x = c1s ∨ x = c2s := by
    have hxsupp : x ∈ pc.support := by
      have hxverts : x ∈ pc.toSubgraph.verts := hpcverts.symm ▸ hx
      exact pc.mem_verts_toSubgraph.mp hxverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlenc] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [c0s] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [c1s] using hxn.symm)
    · exact Or.inr <| Or.inr (by simpa [c2s] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = pc.getVert 3 := hxn.symm
          _ = pc.getVert pc.length := by simpa [hlenc]
          _ = pc.getVert 0 := by rw [pc.getVert_length, pc.getVert_zero]
          _ = c0s := rfl
  have hcover_d {x : Gᶜ.support} (hx : x ∈ d.supp) : x = d0s ∨ x = d1s ∨ x = d2s := by
    have hxsupp : x ∈ pd.support := by
      have hxverts : x ∈ pd.toSubgraph.verts := hpdverts.symm ▸ hx
      exact pd.mem_verts_toSubgraph.mp hxverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlend] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [d0s] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [d1s] using hxn.symm)
    · exact Or.inr <| Or.inr (by simpa [d2s] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = pd.getVert 3 := hxn.symm
          _ = pd.getVert pd.length := by simpa [hlend]
          _ = pd.getVert 0 := by rw [pd.getVert_length, pd.getVert_zero]
          _ = d0s := rfl
  have hcover_support :
      ∀ x : Gᶜ.support, x = c0s ∨ x = c1s ∨ x = c2s ∨ x = d0s ∨ x = d1s ∨ x = d2s := by
    intro x
    have hxunion : x ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hxunion with hxc | hxd
    · rcases hcover_c hxc with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
    · rcases hcover_d hxd with rfl | rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  have htri_c {x y : Gᶜ.support} (hx : x ∈ c.supp) (hy : y ∈ c.supp) (hxy : x ≠ y) :
      H.Adj x y := by
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
  have htri_d {x y : Gᶜ.support} (hx : x ∈ d.supp) (hy : y ∈ d.supp) (hxy : x ≠ y) :
      H.Adj x y := by
    rcases hcover_d hx with rfl | rfl | rfl
    · rcases hcover_d hy with rfl | rfl | rfl
      · exact False.elim (hxy rfl)
      · exact hd01
      · exact hd20.symm
    · rcases hcover_d hy with rfl | rfl | rfl
      · exact hd01.symm
      · exact False.elim (hxy rfl)
      · exact hd12
    · rcases hcover_d hy with rfl | rfl | rfl
      · exact hd20
      · exact hd12.symm
      · exact False.elim (hxy rfl)
  have hc0mem : c0s ∈ c.supp := by
    have : c0s ∈ pc.toSubgraph.verts := by simpa [c0s] using pc.start_mem_verts_toSubgraph
    exact hpcverts ▸ this
  have hc1mem : c1s ∈ c.supp := by
    have hsupp' : c1s ∈ pc.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [c1s], by omega⟩
    exact hpcverts ▸ pc.mem_verts_toSubgraph.mpr hsupp'
  have hc2mem : c2s ∈ c.supp := by
    have hsupp' : c2s ∈ pc.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [c2s], by omega⟩
    exact hpcverts ▸ pc.mem_verts_toSubgraph.mpr hsupp'
  have hd0mem : d0s ∈ d.supp := by
    have : d0s ∈ pd.toSubgraph.verts := by simpa [d0s] using pd.start_mem_verts_toSubgraph
    exact hpdverts ▸ this
  have hd1mem : d1s ∈ d.supp := by
    have hsupp' : d1s ∈ pd.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [d1s], by omega⟩
    exact hpdverts ▸ pd.mem_verts_toSubgraph.mpr hsupp'
  have hd2mem : d2s ∈ d.supp := by
    have hsupp' : d2s ∈ pd.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [d2s], by omega⟩
    exact hpdverts ▸ pd.mem_verts_toSubgraph.mpr hsupp'
  let supportVertex : ∀ x : V, x ≠ u → Gᶜ.support := fun x hxu =>
    ⟨x, by
      have hxcomp : x ∈ ({u} : Set V)ᶜ := by simp [hxu]
      simpa [hsupport] using hxcomp⟩
  let color : V → Fin 4 := fun x =>
    if hxu : x = u then 2
    else if H.connectedComponentMk (supportVertex x hxu) = c then 0 else 1
  have bucket2 {x : V} (hx : color x = 2) : x = u := by
    by_cases hxu : x = u
    · exact hxu
    · by_cases hxc : H.connectedComponentMk (supportVertex x hxu) = c
      · have : False := by simpa [color, hxu, hxc] using hx
        exact False.elim this
      · have : False := by simpa [color, hxu, hxc] using hx
        exact False.elim this
  have bucket0 {x : V} (hxu : x ≠ u) (hx : color x = 0) :
      H.connectedComponentMk (supportVertex x hxu) = c := by
    simp [color, hxu] at hx
    exact hx
  have bucket1 {x : V} (hxu : x ≠ u) (hx : color x = 1) :
      supportVertex x hxu ∈ d.supp := by
    have hnotc : H.connectedComponentMk (supportVertex x hxu) ≠ c := by
      simp [color, hxu] at hx
      exact hx
    have hxunion : supportVertex x hxu ∈ c.supp ∪ d.supp := by
      rw [hunion]
      simp
    rcases hxunion with hxc | hxd
    · exact False.elim
        (hnotc ((SimpleGraph.ConnectedComponent.mem_supp_iff (G := H) (C := c)
          (v := supportVertex x hxu)).1 hxc))
    · exact hxd
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    have hne : x ≠ y := G.ne_of_adj hxy
    by_cases hxu : x = u
    · subst x
      have hcx : color u = 2 := by simp [color]
      have hcy : color y = 2 := by rw [← hEq, hcx]
      rw [bucket2 hcy] at hxy
      exact G.loopless u hxy
    · let xs : Gᶜ.support := supportVertex x hxu
      by_cases hxc : H.connectedComponentMk xs = c
      · have hcx : color x = 0 := by simp [color, hxu, xs, hxc]
        have hcy : color y = 0 := by rw [← hEq, hcx]
        have hyu : y ≠ u := by
          intro hyu
          have : color y = 2 := by simp [color, hyu]
          simpa [this] using hcy
        let ys : Gᶜ.support := supportVertex y hyu
        have hyc : H.connectedComponentMk ys = c := bucket0 hyu hcy
        have hxsys : xs ≠ ys := by
          intro hEqSub
          apply hne
          exact congrArg Subtype.val hEqSub
        have hCompH : H.Adj xs ys := htri_c
          ((SimpleGraph.ConnectedComponent.mem_supp_iff (G := H) (C := c) (v := xs)).2 hxc)
          ((SimpleGraph.ConnectedComponent.mem_supp_iff (G := H) (C := c) (v := ys)).2 hyc)
          hxsys
        have hComp : Gᶜ.Adj x y := by simpa [H, supportVertex, xs, ys] using hCompH
        exact ((SimpleGraph.compl_adj G x y).1 hComp).2 hxy
      · have hcx : color x = 1 := by simp [color, hxu, xs, hxc]
        have hcy : color y = 1 := by rw [← hEq, hcx]
        have hxd : xs ∈ d.supp := bucket1 hxu hcx
        have hyu : y ≠ u := by
          intro hyu
          have : color y = 2 := by simp [color, hyu]
          simpa [this] using hcy
        let ys : Gᶜ.support := supportVertex y hyu
        have hyd : ys ∈ d.supp := bucket1 hyu hcy
        have hxsys : xs ≠ ys := by
          intro hEqSub
          apply hne
          exact congrArg Subtype.val hEqSub
        have hCompH : H.Adj xs ys := htri_d hxd hyd hxsys
        have hComp : Gᶜ.Adj x y := by simpa [H, supportVertex, xs, ys] using hCompH
        exact ((SimpleGraph.compl_adj G x y).1 hComp).2 hxy
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The isolated-support half of the seven-vertex `15`-edge complement split is explicitly
`4`-colorable. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_isolated_compl_support_branch_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    (hiso : ∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    G.Colorable 4 := by
  classical
  rcases hiso with ⟨u, hu0, hsupp, hreg⟩
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
  rcases compl_support_connected_or_exists_distinct_components_card_three_three
      (G := G) hsupp hreg with hconn | ⟨c, d, hcd, hc3, hd3⟩
  · rcases exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
      (G := H) hconn hreg with ⟨v, p, hp, hpverts⟩
    exact colorable_four_of_isolated_compl_vertex_and_compl_support_cycle_covering_all_vertices
      (G := G) hcard hu0 hsupp hp hpverts
  · have hcyc : H.IsCycles := isCycles_of_isRegularOfDegree_two hreg
    let vc : Gᶜ.support := c.nonempty_supp.some
    let vd : Gᶜ.support := d.nonempty_supp.some
    have hvc : vc ∈ c.supp := c.nonempty_supp.some_mem
    have hvd : vd ∈ d.supp := d.nonempty_supp.some_mem
    have hneighc : (H.neighborSet vc).Nonempty := by
      have hdeg : H.degree vc = 2 := hreg vc
      have hdeg_pos : 0 < H.degree vc := by simp [hdeg]
      rcases (H.degree_pos_iff_exists_adj vc).1 hdeg_pos with ⟨w, hw⟩
      exact ⟨w, hw⟩
    have hneighd : (H.neighborSet vd).Nonempty := by
      have hdeg : H.degree vd = 2 := hreg vd
      have hdeg_pos : 0 < H.degree vd := by simp [hdeg]
      rcases (H.degree_pos_iff_exists_adj vd).1 hdeg_pos with ⟨w, hw⟩
      exact ⟨w, hw⟩
    rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := c) hvc hneighc with
      ⟨pc, hpc, hpcverts⟩
    rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := d) hvd hneighd with
      ⟨pd, hpd, hpdverts⟩
    exact colorable_four_of_isolated_compl_vertex_and_compl_support_cycle_components_card_three_three
      (G := G) hcard hu0 hsupp hcd hc3 hd3 hpc hpcverts hpd hpdverts

/-- The isolated-support half of the seven-vertex `15`-edge complement split is impossible for
incidence-critical non-4-colorable graphs. -/
theorem IsIncidenceCriticalNonColorable.not_isolated_compl_support_branch_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ¬ ∃ u : V, Gᶜ.degree u = 0 ∧ Fintype.card Gᶜ.support = 6 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  intro hiso
  exact h.not_colorable
    (h.colorable_four_of_isolated_compl_support_branch_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      hcard hedge hiso)

/-- The seven-vertex `15`-edge complement split reduces to the non-isolated branch. -/
theorem IsIncidenceCriticalNonColorable.fifteen_edge_compl_case_split_reduced_of_card_eq_seven
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 := by
  rcases h.fifteen_edge_compl_case_split_of_card_eq_seven hcard hedge with hiso | hrest
  · exact False.elim
      ((h.not_isolated_compl_support_branch_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
        hcard hedge) hiso)
  · exact hrest

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the reduced seven-vertex `15`-edge complement split. -/
theorem IsVertexCriticalNonColorable.fifteen_edge_compl_case_split_reduced_of_card_eq_seven
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 :=
  h.toIncidenceCritical_four.fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the reduced seven-vertex `15`-edge complement split. -/
theorem IsMinimalNonColorable.fifteen_edge_compl_case_split_reduced_of_card_eq_seven_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 :=
  (h.toIncidenceCritical hadj).fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `15`-edge complement split under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.fifteen_edge_compl_case_split_reduced_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
