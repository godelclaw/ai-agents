import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointDisconnectedColoring
import FourColor.Curriculum.Actual.SevenVertexFifteenIsolatedColoring
import FourColor.Curriculum.Actual.SevenVertexSixteenProfileFourTwoOneStructure

namespace FourColor.Curriculum.Actual

section Helpers

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

@[simp] theorem SimpleGraph.compl_induce_eq_induce
    (s : Set V) :
    ((Gᶜ).induce s)ᶜ = G.induce s := by
  ext a b
  constructor
  · intro h
    rcases (SimpleGraph.compl_adj ((Gᶜ).induce s) a b).1 h with ⟨hne, hnotComp⟩
    have hne_val : (a : V) ≠ b := by
      intro hEq
      exact hne (Subtype.ext hEq)
    have hAdj : G.Adj (a : V) b := by
      by_contra hnotAdj
      exact hnotComp (by
        simpa using (SimpleGraph.compl_adj G (a : V) b).2 ⟨hne_val, hnotAdj⟩)
    exact hAdj
  · intro h
    have hne : a ≠ b := by
      intro hEq
      exact G.loopless (a : V) (hEq ▸ h)
    have hnotComp : ¬ ((Gᶜ).induce s).Adj a b := by
      intro hComp
      exact ((SimpleGraph.compl_adj G (a : V) b).1 (by simpa using hComp)).2 h
    exact (SimpleGraph.compl_adj ((Gᶜ).induce s) a b).2 ⟨hne, hnotComp⟩

@[simp] theorem SimpleGraph.compl_compl (G : SimpleGraph V) : Gᶜᶜ = G := by
  ext a b
  constructor
  · intro h
    rcases (SimpleGraph.compl_adj Gᶜ a b).1 h with ⟨hne, hnot⟩
    by_contra hG
    exact hnot ((SimpleGraph.compl_adj G a b).2 ⟨hne, hG⟩)
  · intro h
    have hne : a ≠ b := G.ne_of_adj h
    have hnot : ¬ Gᶜ.Adj a b := by
      intro hGcompl
      exact ((SimpleGraph.compl_adj G a b).1 hGcompl).2 h
    exact (SimpleGraph.compl_adj Gᶜ a b).2 ⟨hne, hnot⟩

theorem exists_path_data_congr
    {W : Type*} {H K : SimpleGraph W}
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    {u v : W} (hHK : H = K)
    (h :
      ∃ p : H.Walk u v,
        p.IsPath ∧ p.toSubgraph.verts = (H.connectedComponentMk u).supp) :
    ∃ p : K.Walk u v,
      p.IsPath ∧ p.toSubgraph.verts = (K.connectedComponentMk u).supp := by
  subst hHK
  simpa using h

theorem endpoint_cycle_case_split_congr
    {W : Type*} {H K : SimpleGraph W}
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    {u : W} (hHK : H = K)
    (h :
      (H.connectedComponentMk u).supp = Set.univ ∨
        ∃ d : H.ConnectedComponent,
          d ≠ H.connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
          (H.connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : W,
            ∃ q : H.Walk x x,
              q.IsCycle ∧ q.toSubgraph.verts = d.supp) :
    (K.connectedComponentMk u).supp = Set.univ ∨
      ∃ d : K.ConnectedComponent,
        d ≠ K.connectedComponentMk u ∧
        (d.supp.ncard = 3 ∨ d.supp.ncard = 4) ∧
        (K.connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
        ∃ x : W,
          ∃ q : K.Walk x x,
            q.IsCycle ∧ q.toSubgraph.verts = d.supp := by
  subst hHK
  simpa using h

/-- If the complement support is the complement of a singleton and the induced graph on that
support is `3`-colorable, then the whole graph is `4`-colorable by assigning the singleton a fresh
color. -/
theorem colorable_four_of_compl_support_eq_compl_singleton_and_induce_support_colorable_three
    {u : V} (hsupport : Gᶜ.support = ({u} : Set V)ᶜ)
    (hcol : (G.induce Gᶜ.support).Colorable 3) :
    G.Colorable 4 := by
  classical
  rcases hcol with ⟨c⟩
  let supportVertex : ∀ x : V, x ≠ u → Gᶜ.support := fun x hxu =>
    ⟨x, by
      have hxcomp : x ∈ ({u} : Set V)ᶜ := by simp [hxu]
      simpa [hsupport] using hxcomp⟩
  let color : V → Option (Fin 3) := fun x =>
    if hxu : x = u then none else some (c (supportVertex x hxu))
  have hcolor : G.Coloring (Option (Fin 3)) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    have hne : x ≠ y := G.ne_of_adj hxy
    intro hEq
    by_cases hxu : x = u
    · subst x
      have hcx : color u = none := by simp [color]
      have hcy : color y = none := by rw [← hEq, hcx]
      by_cases hyu : y = u
      · exact hne hyu.symm
      · simp [color, hyu] at hcy
    · by_cases hyu : y = u
      · subst y
        have hcy : color u = none := by simp [color]
        have hcx : color x = none := by rw [hEq, hcy]
        simp [color, hxu] at hcx
      · let xs : Gᶜ.support := supportVertex x hxu
        let ys : Gᶜ.support := supportVertex y hyu
        have hcx : color x = some (c xs) := by simp [color, hxu, xs]
        have hcy : color y = some (c ys) := by simp [color, hyu, ys]
        rw [hcx, hcy] at hEq
        have hEqColor : c xs = c ys := Option.some.inj hEq
        have hxy_ind : (G.induce Gᶜ.support).Adj xs ys := hxy
        exact c.valid hxy_ind hEqColor
  simpa [Fintype.card_option] using hcolor.colorable

/-- If the complement has one isolated vertex and support size `6`, any `3`-coloring of the
support induced graph extends to a `4`-coloring of the full seven-vertex graph. -/
theorem colorable_four_of_compl_degree_zero_of_card_support_eq_six_and_induce_support_colorable_three
    (hcard : Fintype.card V = 7) {u : V} (hu0 : Gᶜ.degree u = 0)
    (hsupp : Fintype.card Gᶜ.support = 6)
    (hcol : (G.induce Gᶜ.support).Colorable 3) :
    G.Colorable 4 := by
  have hsupport :
      Gᶜ.support = ({u} : Set V)ᶜ :=
    compl_support_eq_compl_singleton_of_card_eq_seven_of_compl_degree_eq_zero_of_card_support_eq_six
      (G := G) hcard hu0 hsupp
  exact
    colorable_four_of_compl_support_eq_compl_singleton_and_induce_support_colorable_three
      (G := G) hsupport hcol

end Helpers

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the complement is a spanning path on six vertices, then the graph is `3`-colorable. -/
theorem colorable_three_of_compl_path_covering_all_vertices_of_card_eq_six
    (hcard : Fintype.card V = 6)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = Set.univ) :
    G.Colorable 3 := by
  classical
  have hlen : p.length = 5 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let a3 : V := p.getVert 3
  let a4 : V := p.getVert 4
  let a5 : V := p.getVert 5
  have hget_ne :
      ∀ {m n : ℕ}, m ≤ 5 → n ≤ 5 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hp.getVert_injOn
      (by simpa [hlen] using hm)
      (by simpa [hlen] using hn)
      hEq
  have h20 : a2 ≠ a0 := by
    simpa [a2, a0] using hget_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have h21 : a2 ≠ a1 := by
    simpa [a2, a1] using hget_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have h30 : a3 ≠ a0 := by
    simpa [a3, a0] using hget_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have h31 : a3 ≠ a1 := by
    simpa [a3, a1] using hget_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have h40 : a4 ≠ a0 := by
    simpa [a4, a0] using hget_ne (m := 4) (n := 0) (by decide) (by decide) (by decide)
  have h41 : a4 ≠ a1 := by
    simpa [a4, a1] using hget_ne (m := 4) (n := 1) (by decide) (by decide) (by decide)
  have h42 : a4 ≠ a2 := by
    simpa [a4, a2] using hget_ne (m := 4) (n := 2) (by decide) (by decide) (by decide)
  have h43 : a4 ≠ a3 := by
    simpa [a4, a3] using hget_ne (m := 4) (n := 3) (by decide) (by decide) (by decide)
  have h50 : a5 ≠ a0 := by
    simpa [a5, a0] using hget_ne (m := 5) (n := 0) (by decide) (by decide) (by decide)
  have h51 : a5 ≠ a1 := by
    simpa [a5, a1] using hget_ne (m := 5) (n := 1) (by decide) (by decide) (by decide)
  have h52 : a5 ≠ a2 := by
    simpa [a5, a2] using hget_ne (m := 5) (n := 2) (by decide) (by decide) (by decide)
  have h53 : a5 ≠ a3 := by
    simpa [a5, a3] using hget_ne (m := 5) (n := 3) (by decide) (by decide) (by decide)
  have h54 : a5 ≠ a4 := by
    simpa [a5, a4] using hget_ne (m := 5) (n := 4) (by decide) (by decide) (by decide)
  have h01 : (Gᶜ).Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have h23 : (Gᶜ).Adj a2 a3 := by
    have h2 : 2 < p.length := by omega
    simpa [a2, a3] using p.adj_getVert_succ h2
  have h45 : (Gᶜ).Adj a4 a5 := by
    have h4 : 4 < p.length := by omega
    simpa [a4, a5] using p.adj_getVert_succ h4
  have hcover : ∀ x : V, x = a0 ∨ x = a1 ∨ x = a2 ∨ x = a3 ∨ x = a4 ∨ x = a5 := by
    intro x
    have hxverts : x ∈ p.toSubgraph.verts := by rw [hpverts]; simp
    have hxsupp : x ∈ p.support := p.mem_verts_toSubgraph.mp hxverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn5 : n ≤ 5 := by simpa [hlen] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [a0] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [a2] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a3] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a4] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        (by simpa [a5] using hxn.symm)
  let color : V → Fin 3 := fun x =>
    if x = a0 ∨ x = a1 then 0
    else if x = a2 ∨ x = a3 then 1
    else 2
  have hcolor_a0 : color a0 = 0 := by simp [color]
  have hcolor_a1 : color a1 = 0 := by simp [color]
  have hcolor_a2 : color a2 = 1 := by simp [color, h20, h21]
  have hcolor_a3 : color a3 = 1 := by simp [color, h30, h31]
  have hcolor_a4 : color a4 = 2 := by simp [color, h40, h41, h42, h43]
  have hcolor_a5 : color a5 = 2 := by simp [color, h50, h51, h52, h53, h54]
  have bucket0 {x : V} (hx : color x = 0) : x = a0 ∨ x = a1 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl
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
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl
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
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl
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
  have hcolor : G.Coloring (Fin 3) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    by_cases hx0 : color x = 0
    · have hy0 : color y = 0 := by rw [← hEq, hx0]
      rcases bucket0 hx0 with rfl | rfl
      · rcases bucket0 hy0 with rfl | rfl
        · exact (G.ne_of_adj hxy) rfl
        · exact ((SimpleGraph.compl_adj G a0 a1).1 h01).2 hxy
      · rcases bucket0 hy0 with rfl | rfl
        · exact ((SimpleGraph.compl_adj G a1 a0).1 h01.symm).2 hxy
        · exact (G.ne_of_adj hxy) rfl
    · by_cases hx1 : color x = 1
      · have hy1 : color y = 1 := by rw [← hEq, hx1]
        rcases bucket1 hx1 with rfl | rfl
        · rcases bucket1 hy1 with rfl | rfl
          · exact (G.ne_of_adj hxy) rfl
          · exact ((SimpleGraph.compl_adj G a2 a3).1 h23).2 hxy
        · rcases bucket1 hy1 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G a3 a2).1 h23.symm).2 hxy
          · exact (G.ne_of_adj hxy) rfl
      · have hx2 : color x = 2 := by
          rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl
          · exact False.elim (hx0 hcolor_a0)
          · exact False.elim (hx0 hcolor_a1)
          · exact False.elim (hx1 hcolor_a2)
          · exact False.elim (hx1 hcolor_a3)
          · exact hcolor_a4
          · exact hcolor_a5
        have hy2 : color y = 2 := by rw [← hEq, hx2]
        rcases bucket2 hx2 with rfl | rfl
        · rcases bucket2 hy2 with rfl | rfl
          · exact (G.ne_of_adj hxy) rfl
          · exact ((SimpleGraph.compl_adj G a4 a5).1 h45).2 hxy
        · rcases bucket2 hy2 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G a5 a4).1 h45.symm).2 hxy
          · exact (G.ne_of_adj hxy) rfl
  exact hcolor.colorable

/-- If the complement splits as a `3`-vertex path component and a `3`-vertex cycle component,
then the graph is `3`-colorable. -/
theorem colorable_three_of_compl_path_component_card_three_and_cycle_component_card_three
    (hcard : Fintype.card V = 6)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp)
    {d : (Gᶜ).ConnectedComponent} (hcd : d ≠ (Gᶜ).connectedComponentMk u)
    (hd3 : d.supp.ncard = 3)
    (hunion : ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ)
    {x : V} {q : (Gᶜ).Walk x x} (hq : q.IsCycle) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 3 := by
  classical
  let c : (Gᶜ).ConnectedComponent := (Gᶜ).connectedComponentMk u
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ))
      (by simpa [c] using hcd.symm)
  have hc3 : c.supp.ncard = 3 := by
    have hsum : c.supp.ncard + d.supp.ncard = 6 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj]
        _ = 6 := by
          rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    omega
  have hlenp : p.length = 2 := by
    simpa [hpverts, c, hc3] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 3 := by
    simpa [hd3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  have hgetp_ne :
      ∀ {m n : ℕ}, m ≤ 2 → n ≤ 2 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hp.getVert_injOn (by simpa [hlenp] using hm) (by simpa [hlenp] using hn) hEq
  have ha20 : a2 ≠ a0 := by
    simpa [a2, a0] using hgetp_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have ha21 : a2 ≠ a1 := by
    simpa [a2, a1] using hgetp_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
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
  have ha0mem : a0 ∈ c.supp := by
    have : a0 ∈ p.toSubgraph.verts := by simpa [a0] using p.start_mem_verts_toSubgraph
    exact hpverts ▸ this
  have ha1mem : a1 ∈ c.supp := by
    have hsupp' : a1 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [a1], by omega⟩
    have : a1 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp'
    exact hpverts ▸ this
  have ha2mem : a2 ∈ c.supp := by
    have hsupp' : a2 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [a2], by omega⟩
    have : a2 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp'
    exact hpverts ▸ this
  have ha0notd : a0 ∉ d.supp := Set.disjoint_left.mp hdisj ha0mem
  have ha1notd : a1 ∉ d.supp := Set.disjoint_left.mp hdisj ha1mem
  have ha2notd : a2 ∉ d.supp := Set.disjoint_left.mp hdisj ha2mem
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
      ∀ y : V, y ∈ d.supp ∨ y = a0 ∨ y = a1 ∨ y = a2 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · rcases hcover_c hyc with rfl | rfl | rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr rfl
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
  let color : V → Fin 3 := fun y =>
    if y ∈ d.supp then 0 else if y = a0 ∨ y = a1 then 1 else 2
  have hcolor_d {y : V} (hy : y ∈ d.supp) : color y = 0 := by
    unfold color
    rw [if_pos hy]
  have hcolor_a0 : color a0 = 1 := by
    unfold color
    rw [if_neg ha0notd, if_pos (Or.inl rfl)]
  have hcolor_a1 : color a1 = 1 := by
    unfold color
    rw [if_neg ha1notd, if_pos (Or.inr rfl)]
  have hcolor_a2 : color a2 = 2 := by
    have hnot : ¬ (a2 = a0 ∨ a2 = a1) := by
      intro hEq
      rcases hEq with hEq | hEq
      · exact ha20 hEq
      · exact ha21 hEq
    unfold color
    rw [if_neg ha2notd, if_neg hnot]
  have bucket0 {y : V} (hy : color y = 0) : y ∈ d.supp := by
    rcases hcover y with hyd | rfl | rfl | rfl
    · exact hyd
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
  have bucket1 {y : V} (hy : color y = 1) : y = a0 ∨ y = a1 := by
    rcases hcover y with hyd | rfl | rfl | rfl
    · have : False := by simpa [hcolor_d hyd] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a2] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y = a2 := by
    rcases hcover y with hyd | rfl | rfl | rfl
    · have : False := by simpa [hcolor_d hyd] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hy
      exact False.elim this
    · rfl
  have hcolor : G.Coloring (Fin 3) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hEq, hy0]
      exact ((SimpleGraph.compl_adj G y z).1 (htri (bucket0 hy0) (bucket0 hz0) (G.ne_of_adj hyz))).2 hyz
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hEq, hy1]
        rcases bucket1 hy1 with rfl | rfl
        · rcases bucket1 hz1 with rfl | rfl
          · exact (G.ne_of_adj hyz) rfl
          · exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
        · rcases bucket1 hz1 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
          · exact (G.ne_of_adj hyz) rfl
      · have hy2 : color y = 2 := by
          rcases hcover y with hyd | rfl | rfl | rfl
          · exact False.elim (hy0 (hcolor_d hyd))
          · exact False.elim (hy1 hcolor_a0)
          · exact False.elim (hy1 hcolor_a1)
          · exact hcolor_a2
        have hz2 : color z = 2 := by rw [← hEq, hy2]
        rw [bucket2 hy2, bucket2 hz2] at hyz
        exact G.loopless a2 hyz
  exact hcolor.colorable

/-- If the complement splits as a `2`-vertex path component and a `4`-vertex cycle component,
then the graph is `3`-colorable. -/
theorem colorable_three_of_compl_path_component_card_two_and_cycle_component_card_four
    (hcard : Fintype.card V = 6)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath)
    (hpverts : p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp)
    {d : (Gᶜ).ConnectedComponent} (hcd : d ≠ (Gᶜ).connectedComponentMk u)
    (hd4 : d.supp.ncard = 4)
    (hunion : ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ)
    {x : V} {q : (Gᶜ).Walk x x} (hq : q.IsCycle) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 3 := by
  classical
  let c : (Gᶜ).ConnectedComponent := (Gᶜ).connectedComponentMk u
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ))
      (by simpa [c] using hcd.symm)
  have hc2 : c.supp.ncard = 2 := by
    have hsum : c.supp.ncard + d.supp.ncard = 6 := by
      calc
        c.supp.ncard + d.supp.ncard = (c.supp ∪ d.supp).ncard := by
          rw [Set.ncard_union_eq hdisj]
        _ = 6 := by
          rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    omega
  have hlenp : p.length = 1 := by
    simpa [hpverts, c, hc2] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 4 := by
    simpa [hd4] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  let b3 : V := q.getVert 3
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
    have hsupp' : a1 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [a1], by omega⟩
    have : a1 ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hsupp'
    exact hpverts ▸ this
  have ha0notd : a0 ∉ d.supp := Set.disjoint_left.mp hdisj ha0mem
  have ha1notd : a1 ∉ d.supp := Set.disjoint_left.mp hdisj ha1mem
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
      ∀ y : V, y = a0 ∨ y = a1 ∨ y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · rcases hcover_c hyc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr <| Or.inl rfl
    · rcases hcover_d hyd with rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  let color : V → Fin 3 := fun y =>
    if y = a0 ∨ y = a1 then 0
    else if y = b0 ∨ y = b1 then 1
    else 2
  have hcolor_a0 : color a0 = 0 := by simp [color]
  have hcolor_a1 : color a1 = 0 := by simp [color]
  have hb0mem : b0 ∈ d.supp := by
    have : b0 ∈ q.toSubgraph.verts := by simpa [b0] using q.start_mem_verts_toSubgraph
    exact hqverts ▸ this
  have hb1mem : b1 ∈ d.supp := by
    have hsupp' : b1 ∈ q.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨1, by simp [b1], by omega⟩
    have : b1 ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hsupp'
    exact hqverts ▸ this
  have hb0a0 : b0 ≠ a0 := by
    intro hEq
    exact ha0notd (hEq.symm ▸ hb0mem)
  have hb0a1 : b0 ≠ a1 := by
    intro hEq
    exact ha1notd (hEq.symm ▸ hb0mem)
  have hb1a0 : b1 ≠ a0 := by
    intro hEq
    exact ha0notd (hEq.symm ▸ hb1mem)
  have hb1a1 : b1 ≠ a1 := by
    intro hEq
    exact ha1notd (hEq.symm ▸ hb1mem)
  have hcolor_b0 : color b0 = 1 := by
    simp [color, hb0a0, hb0a1]
  have hcolor_b1 : color b1 = 1 := by
    simp [color, hb1a0, hb1a1]
  have hcolor_b2 : color b2 = 2 := by
    have hb2a0 : b2 ≠ a0 := by intro hEq; exact ha0notd (hEq.symm ▸ by
      have : b2 ∈ d.supp := by
        have hsupp' : b2 ∈ q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [b2], by omega⟩
        exact hqverts ▸ q.mem_verts_toSubgraph.mpr hsupp'
      exact this)
    have hb2a1 : b2 ≠ a1 := by intro hEq; exact ha1notd (hEq.symm ▸ by
      have : b2 ∈ d.supp := by
        have hsupp' : b2 ∈ q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [b2], by omega⟩
        exact hqverts ▸ q.mem_verts_toSubgraph.mpr hsupp'
      exact this)
    simp [color, hb2a0, hb2a1, hb20, hb21]
  have hcolor_b3 : color b3 = 2 := by
    have hb3a0 : b3 ≠ a0 := by intro hEq; exact ha0notd (hEq.symm ▸ by
      have : b3 ∈ d.supp := by
        have hsupp' : b3 ∈ q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [b3], by omega⟩
        exact hqverts ▸ q.mem_verts_toSubgraph.mpr hsupp'
      exact this)
    have hb3a1 : b3 ≠ a1 := by intro hEq; exact ha1notd (hEq.symm ▸ by
      have : b3 ∈ d.supp := by
        have hsupp' : b3 ∈ q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨3, by simp [b3], by omega⟩
        exact hqverts ▸ q.mem_verts_toSubgraph.mpr hsupp'
      exact this)
    simp [color, hb3a0, hb3a1, hb30, hb31]
  have bucket0 {y : V} (hy : color y = 0) : y = a0 ∨ y = a1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl
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
  have bucket1 {y : V} (hy : color y = 1) : y = b0 ∨ y = b1 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl
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
  have bucket2 {y : V} (hy : color y = 2) : y = b2 ∨ y = b3 := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl
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
  have hcolor : G.Coloring (Fin 3) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hEq, hy0]
      rcases bucket0 hy0 with rfl | rfl
      · rcases bucket0 hz0 with rfl | rfl
        · exact (G.ne_of_adj hyz) rfl
        · exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
      · rcases bucket0 hz0 with rfl | rfl
        · exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
        · exact (G.ne_of_adj hyz) rfl
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hEq, hy1]
        rcases bucket1 hy1 with rfl | rfl
        · rcases bucket1 hz1 with rfl | rfl
          · exact (G.ne_of_adj hyz) rfl
          · exact ((SimpleGraph.compl_adj G b0 b1).1 hb01).2 hyz
        · rcases bucket1 hz1 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G b1 b0).1 hb01.symm).2 hyz
          · exact (G.ne_of_adj hyz) rfl
      · have hy2 : color y = 2 := by
          rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl
          · exact False.elim (hy0 hcolor_a0)
          · exact False.elim (hy0 hcolor_a1)
          · exact False.elim (hy1 hcolor_b0)
          · exact False.elim (hy1 hcolor_b1)
          · exact hcolor_b2
          · exact hcolor_b3
        have hz2 : color z = 2 := by rw [← hEq, hy2]
        rcases bucket2 hy2 with rfl | rfl
        · rcases bucket2 hz2 with rfl | rfl
          · exact (G.ne_of_adj hyz) rfl
          · exact ((SimpleGraph.compl_adj G b2 b3).1 hb23).2 hyz
        · rcases bucket2 hz2 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G b3 b2).1 hb23.symm).2 hyz
          · exact (G.ne_of_adj hyz) rfl
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The seven-vertex `16`-edge degree-count profile `(4,2,1)` is explicitly `4`-colorable.

Source: new theorem combining the isolated complement vertex with the support-shape split
`P₆ ∨ (P₃ ⊔ C₃) ∨ (P₂ ⊔ C₄)`, then extending a `3`-coloring of the six-vertex support by one
fresh color. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_profile_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    G.Colorable 4 := by
  classical
  rcases
      h.exists_distinct_compl_degree_zero_one_one_card_support_eq_six_forall_rest_degree_two_of_profile_four_two_one
        hcard hedge hprof with
    ⟨z, _u, _v, _hzu, _hzv, _huv, hz0, _hu1, _hv1, hsupp, _hrest⟩
  rcases
      h.exists_isolated_vertex_and_support_path_cycle_case_split_of_profile_four_two_one
        hcard hedge hprof with
    ⟨_z, _hz0', u, v, _huv, _hu1, _hv1, _hrest, p, hp, hpverts, hsplit⟩
  have hcol_support : (G.induce Gᶜ.support).Colorable 3 := by
    let H : SimpleGraph Gᶜ.support := (Gᶜ).induce Gᶜ.support
    have hcol_support_compl : Hᶜ.Colorable 3 := by
      have hpdata :
          ∃ p' : Hᶜᶜ.Walk u v,
            p'.IsPath ∧ p'.toSubgraph.verts = (Hᶜᶜ.connectedComponentMk u).supp := by
        exact
          exists_path_data_congr
            (H := H) (K := Hᶜᶜ) (u := u) (v := v)
            (SimpleGraph.compl_compl H).symm
            ⟨p, hp, hpverts⟩
      rcases hpdata with ⟨p', hp', hpverts'⟩
      have hsplit' :
          (Hᶜᶜ.connectedComponentMk u).supp = Set.univ ∨
            ∃ d' : Hᶜᶜ.ConnectedComponent,
              d' ≠ Hᶜᶜ.connectedComponentMk u ∧
              (d'.supp.ncard = 3 ∨ d'.supp.ncard = 4) ∧
              (Hᶜᶜ.connectedComponentMk u).supp ∪ d'.supp = Set.univ ∧
              ∃ x : Gᶜ.support,
                ∃ q' : Hᶜᶜ.Walk x x,
                  q'.IsCycle ∧ q'.toSubgraph.verts = d'.supp := by
        exact
          endpoint_cycle_case_split_congr
            (H := H) (K := Hᶜᶜ) (u := u)
            (SimpleGraph.compl_compl H).symm
            hsplit
      rcases hsplit' with hfull | ⟨d', hcd', hd', hunion', x, q', hq', hqverts'⟩
      · exact
          colorable_three_of_compl_path_covering_all_vertices_of_card_eq_six
            (G := Hᶜ) (u := u) (v := v) (p := p')
            hsupp hp' (by simpa using hpverts'.trans hfull)
      · rcases hd' with hd3 | hd4
        · exact
            colorable_three_of_compl_path_component_card_three_and_cycle_component_card_three
              (G := Hᶜ) (u := u) (v := v) (p := p')
              hsupp hp' hpverts' (d := d') hcd' hd3 hunion' (x := x) (q := q') hq' hqverts'
        · exact
            colorable_three_of_compl_path_component_card_two_and_cycle_component_card_four
              (G := Hᶜ) (u := u) (v := v) (p := p')
              hsupp hp' hpverts' (d := d') hcd' hd4 hunion' (x := x) (q := q') hq' hqverts'
    simpa [H] using hcol_support_compl
  exact
    colorable_four_of_compl_degree_zero_of_card_support_eq_six_and_induce_support_colorable_three
      (G := G) hcard hz0 hsupp hcol_support

/-- The seven-vertex `16`-edge degree-count profile `(4,2,1)` cannot occur in an incidence-critical
non-`4`-colorable graph.

Source: immediate contradiction from the explicit `4`-coloring of the profile. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) := by
  intro hprof
  exact h.not_colorable
    (h.colorable_four_of_profile_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      hcard hedge hprof)

/-- After excluding `(4,2,1)`, the seven-vertex `16`-edge degree-count split reduces to the two
profiles `(3,4,0)` and `(5,0,2)`. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  rcases h.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen hcard hedge with
    hcase | hcase | hcase
  · exact Or.inl hcase
  · exfalso
    exact
      (h.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge) hcase
  · exact Or.inr hcase

/-- Live seven-vertex `K₅`-free degree-count split after excluding the `(4,2,1)` profile. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact h.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    hcard hedge

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift excluding the seven-vertex `16`-edge `(4,2,1)` profile. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge

/-- Vertex-critical lift of the reduced seven-vertex `16`-edge degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge

/-- Vertex-critical lift of the live reduced seven-vertex `K₅`-free degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift excluding the seven-vertex `16`-edge `(4,2,1)` profile. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift excluding the live seven-vertex `K₅`-free profile `(4,2,1)`
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_two_one_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `16`-edge degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the live reduced seven-vertex `K₅`-free degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the live reduced seven-vertex `K₅`-free degree-count split
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
