import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointDisconnectedColoring
import FourColor.Curriculum.Actual.SevenVertexSixteenProfileFourTwoOneColoring
import FourColor.Curriculum.Actual.SevenVertexSixteenProfileThreeFourZeroCases

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a `2`-vertex path component, the two distinct component vertices are adjacent.

Source: helper theorem for the seven-vertex `|E| = 16` profile `(3,4,0)`, used to color the
`P₂` pieces in the exact complement-shape split. -/
theorem adj_of_mem_path_component_card_two
    {c : (Gᶜ).ConnectedComponent} (hc2 : c.supp.ncard = 2)
    {u v : V} {p : (Gᶜ).Walk u v} (hp : p.IsPath) (hpverts : p.toSubgraph.verts = c.supp)
    {x y : V} (hx : x ∈ c.supp) (hy : y ∈ c.supp) (hxy : x ≠ y) :
    (Gᶜ).Adj x y := by
  have hlenp : p.length = 1 := by
    simpa [hc2] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  have ha01 : (Gᶜ).Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have hcover_c {z : V} (hz : z ∈ c.supp) : z = a0 ∨ z = a1 := by
    have hzsupp : z ∈ p.support := by
      have hzverts : z ∈ p.toSubgraph.verts := hpverts.symm ▸ hz
      exact p.mem_verts_toSubgraph.mp hzverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzsupp with ⟨n, hzn, hn⟩
    have hn1 : n ≤ 1 := by simpa [hlenp] using hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inl (by simpa [a0] using hzn.symm)
    · exact Or.inr (by simpa [a1] using hzn.symm)
  rcases hcover_c hx with rfl | rfl
  · rcases hcover_c hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact ha01
  · rcases hcover_c hy with rfl | rfl
    · exact ha01.symm
    · exact False.elim (hxy rfl)

/-- In a `3`-cycle component, any two distinct component vertices are adjacent.

Source: helper theorem for the seven-vertex `|E| = 16` profile `(3,4,0)`, used to color the
`C₃` piece in the exact complement-shape split. -/
theorem adj_of_mem_cycle_component_card_three
    {e : (Gᶜ).ConnectedComponent} (he3 : e.supp.ncard = 3)
    {x : V} {r : (Gᶜ).Walk x x} (hr : r.IsCycle) (hrverts : r.toSubgraph.verts = e.supp)
    {y z : V} (hy : y ∈ e.supp) (hz : z ∈ e.supp) (hyz : y ≠ z) :
    (Gᶜ).Adj y z := by
  have hlenr : r.length = 3 := by
    simpa [he3] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hr hrverts)
  let b0 : V := r.getVert 0
  let b1 : V := r.getVert 1
  let b2 : V := r.getVert 2
  have hb01 : (Gᶜ).Adj b0 b1 := by
    have h0 : 0 < r.length := by omega
    simpa [b0, b1] using r.adj_getVert_succ h0
  have hb12 : (Gᶜ).Adj b1 b2 := by
    have h1 : 1 < r.length := by omega
    simpa [b1, b2] using r.adj_getVert_succ h1
  have hb20 : (Gᶜ).Adj b2 b0 := by
    have h2 : 2 < r.length := by omega
    have hb20' : (Gᶜ).Adj (r.getVert 2) (r.getVert r.length) := by
      simpa [hlenr] using r.adj_getVert_succ h2
    simpa [b2, b0, r.getVert_zero, r.getVert_length] using hb20'
  have hcover_e {w : V} (hw : w ∈ e.supp) : w = b0 ∨ w = b1 ∨ w = b2 := by
    have hwsupp : w ∈ r.support := by
      have hwverts : w ∈ r.toSubgraph.verts := hrverts.symm ▸ hw
      exact r.mem_verts_toSubgraph.mp hwverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwsupp with ⟨n, hwn, hn⟩
    have hn3 : n ≤ 3 := by simpa [hlenr] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [b0] using hwn.symm)
    · exact Or.inr <| Or.inl (by simpa [b1] using hwn.symm)
    · exact Or.inr <| Or.inr (by simpa [b2] using hwn.symm)
    · exact Or.inl <| by
        calc
          w = r.getVert 3 := hwn.symm
          _ = r.getVert r.length := by simpa [hlenr]
          _ = r.getVert 0 := by rw [r.getVert_length, r.getVert_zero]
          _ = b0 := rfl
  rcases hcover_e hy with rfl | rfl | rfl
  · rcases hcover_e hz with rfl | rfl | rfl
    · exact False.elim (hyz rfl)
    · exact hb01
    · exact hb20.symm
  · rcases hcover_e hz with rfl | rfl | rfl
    · exact hb01.symm
    · exact False.elim (hyz rfl)
    · exact hb12
  · rcases hcover_e hz with rfl | rfl | rfl
    · exact hb20
    · exact hb12.symm
    · exact False.elim (hyz rfl)

/-- If the complement splits as `P₂ ⊔ P₅`, then the original graph is `4`-colorable.

Source: explicit coloring for the seven-vertex `16`-edge profile `(3,4,0)` case
`P₂ ⊔ P₅`. -/
theorem colorable_four_of_compl_path_components_card_two_five
    (hcard : Fintype.card V = 7)
    {c d : (Gᶜ).ConnectedComponent} (hcd : c ≠ d)
    (hc2 : c.supp.ncard = 2) (hd5 : d.supp.ncard = 5)
    (hunion : c.supp ∪ d.supp = Set.univ)
    {u₁ v₁ : V} {p : (Gᶜ).Walk u₁ v₁} (hp : p.IsPath) (hpverts : p.toSubgraph.verts = c.supp)
    {u₂ v₂ : V} {q : (Gᶜ).Walk u₂ v₂} (hq : q.IsPath) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hcd
  have hlenq : q.length = 4 := by
    simpa [hd5] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
  let b0 : V := q.getVert 0
  let b1 : V := q.getVert 1
  let b2 : V := q.getVert 2
  let b3 : V := q.getVert 3
  let b4 : V := q.getVert 4
  have hgetq_ne :
      ∀ {m n : ℕ}, m ≤ 4 → n ≤ 4 → m ≠ n → q.getVert m ≠ q.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hq.getVert_injOn (by simpa [hlenq] using hm) (by simpa [hlenq] using hn) hEq
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
  have hb01 : (Gᶜ).Adj b0 b1 := by
    have h0 : 0 < q.length := by omega
    simpa [b0, b1] using q.adj_getVert_succ h0
  have hb23 : (Gᶜ).Adj b2 b3 := by
    have h2 : 2 < q.length := by omega
    simpa [b2, b3] using q.adj_getVert_succ h2
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
  have hcover_d {y : V} (hy : y ∈ d.supp) :
      y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 ∨ y = b4 := by
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
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [b3] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
        (by simpa [b4] using hyn.symm)
  have hcover : ∀ y : V, y ∈ c.supp ∨ y = b0 ∨ y = b1 ∨ y = b2 ∨ y = b3 ∨ y = b4 := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hyunion with hyc | hyd
    · exact Or.inl hyc
    · rcases hcover_d hyd with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  let color : V → Fin 4 := fun y =>
    if y ∈ c.supp then 0
    else if y = b0 ∨ y = b1 then 1
    else if y = b2 ∨ y = b3 then 2
    else 3
  have hcolor_c {y : V} (hy : y ∈ c.supp) : color y = 0 := by
    unfold color
    rw [if_pos hy]
  have hcolor_b0 : color b0 = 1 := by
    unfold color
    rw [if_neg hb0notc, if_pos (Or.inl rfl)]
  have hcolor_b1 : color b1 = 1 := by
    unfold color
    rw [if_neg hb1notc, if_pos (Or.inr rfl)]
  have hcolor_b2 : color b2 = 2 := by
    unfold color
    rw [if_neg hb2notc, if_neg (by
      intro h
      rcases h with h | h
      · exact hb20 h
      · exact hb21 h), if_pos (Or.inl rfl)]
  have hcolor_b3 : color b3 = 2 := by
    unfold color
    rw [if_neg hb3notc, if_neg (by
      intro h
      rcases h with h | h
      · exact hb30 h
      · exact hb31 h), if_pos (Or.inr rfl)]
  have hcolor_b4 : color b4 = 3 := by
    unfold color
    rw [if_neg hb4notc, if_neg (by
      intro h
      rcases h with h | h
      · exact hb40 h
      · exact hb41 h), if_neg (by
      intro h
      rcases h with h | h
      · exact hb42 h
      · exact hb43 h)]
  have bucket0 {y : V} (hy : color y = 0) : y ∈ c.supp := by
    by_cases hyc : y ∈ c.supp
    · exact hyc
    · rcases hcover y with hyc' | rfl | rfl | rfl | rfl | rfl
      · contradiction
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
    rcases hcover y with hyc | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_c hyc] using hy
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
    rcases hcover y with hyc | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_c hyc] using hy
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
    rcases hcover y with hyc | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_c hyc] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b0] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b1] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b2] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b3] using hy
      exact False.elim this
    · exact rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      exact
        ((SimpleGraph.compl_adj G y z).1
          (adj_of_mem_path_component_card_two
            (G := G) hc2 hp hpverts (bucket0 hy0) (bucket0 hz0) (G.ne_of_adj hyz))).2 hyz
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rcases bucket1 hy1 with rfl | rfl
        · rcases bucket1 hz1 with rfl | rfl
          · exact (G.ne_of_adj hyz) rfl
          · exact ((SimpleGraph.compl_adj G b0 b1).1 hb01).2 hyz
        · rcases bucket1 hz1 with rfl | rfl
          · exact ((SimpleGraph.compl_adj G b1 b0).1 hb01.symm).2 hyz
          · exact (G.ne_of_adj hyz) rfl
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with rfl | rfl
          · rcases bucket2 hz2 with rfl | rfl
            · exact (G.ne_of_adj hyz) rfl
            · exact ((SimpleGraph.compl_adj G b2 b3).1 hb23).2 hyz
          · rcases bucket2 hz2 with rfl | rfl
            · exact ((SimpleGraph.compl_adj G b3 b2).1 hb23.symm).2 hyz
            · exact (G.ne_of_adj hyz) rfl
        · have hy3 : color y = 3 := by
            rcases hcover y with hyc | rfl | rfl | rfl | rfl | rfl
            · exact False.elim (hy0 (hcolor_c hyc))
            · exact False.elim (hy1 hcolor_b0)
            · exact False.elim (hy1 hcolor_b1)
            · exact False.elim (hy2 hcolor_b2)
            · exact False.elim (hy2 hcolor_b3)
            · exact hcolor_b4
          have hz3 : color z = 3 := by rw [← hyzEq, hy3]
          rw [bucket3 hy3, bucket3 hz3] at hyz
          exact G.loopless b4 hyz
  exact hcolor.colorable

/-- If the complement splits as `P₃ ⊔ P₄`, then the original graph is `4`-colorable.

Source: explicit coloring for the seven-vertex `16`-edge profile `(3,4,0)` case
`P₃ ⊔ P₄`. -/
theorem colorable_four_of_compl_path_components_card_three_four
    (hcard : Fintype.card V = 7)
    {c d : (Gᶜ).ConnectedComponent} (hcd : c ≠ d)
    (hc3 : c.supp.ncard = 3) (hd4 : d.supp.ncard = 4)
    (hunion : c.supp ∪ d.supp = Set.univ)
    {u₁ v₁ : V} {p : (Gᶜ).Walk u₁ v₁} (hp : p.IsPath) (hpverts : p.toSubgraph.verts = c.supp)
    {u₂ v₂ : V} {q : (Gᶜ).Walk u₂ v₂} (hq : q.IsPath) (hqverts : q.toSubgraph.verts = d.supp) :
    G.Colorable 4 := by
  classical
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hcd
  have hlenp : p.length = 2 := by
    simpa [hc3] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  have hlenq : q.length = 3 := by
    simpa [hd4] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hq hqverts)
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
    apply hmn
    exact hq.getVert_injOn (by simpa [hlenq] using hm) (by simpa [hlenq] using hn) hEq
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
    have hn3 : n ≤ 3 := by simpa [hlenq] using hn
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [b0] using hyn.symm)
    · exact Or.inr <| Or.inl (by simpa [b1] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [b2] using hyn.symm)
    · exact Or.inr <| Or.inr <| Or.inr (by simpa [b3] using hyn.symm)
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
    · exact rfl
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
      rcases bucket0 hy0 with rfl | rfl
      · rcases bucket0 hz0 with rfl | rfl
        · exact (G.ne_of_adj hyz) rfl
        · exact ((SimpleGraph.compl_adj G a0 a1).1 ha01).2 hyz
      · rcases bucket0 hz0 with rfl | rfl
        · exact ((SimpleGraph.compl_adj G a1 a0).1 ha01.symm).2 hyz
        · exact (G.ne_of_adj hyz) rfl
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rw [bucket1 hy1, bucket1 hz1] at hyz
        exact G.loopless a2 hyz
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with rfl | rfl
          · rcases bucket2 hz2 with rfl | rfl
            · exact (G.ne_of_adj hyz) rfl
            · exact ((SimpleGraph.compl_adj G b0 b1).1 hb01).2 hyz
          · rcases bucket2 hz2 with rfl | rfl
            · exact ((SimpleGraph.compl_adj G b1 b0).1 hb01.symm).2 hyz
            · exact (G.ne_of_adj hyz) rfl
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
          rcases bucket3 hy3 with rfl | rfl
          · rcases bucket3 hz3 with rfl | rfl
            · exact (G.ne_of_adj hyz) rfl
            · exact ((SimpleGraph.compl_adj G b2 b3).1 hb23).2 hyz
          · rcases bucket3 hz3 with rfl | rfl
            · exact ((SimpleGraph.compl_adj G b3 b2).1 hb23.symm).2 hyz
            · exact (G.ne_of_adj hyz) rfl
  exact hcolor.colorable

/-- If the complement splits as `P₂ ⊔ P₂ ⊔ C₃`, then the original graph is `3`-colorable.

Source: explicit coloring for the seven-vertex `16`-edge profile `(3,4,0)` case
`P₂ ⊔ P₂ ⊔ C₃`. -/
theorem colorable_three_of_compl_path_components_card_two_two_and_cycle_component_card_three
    (hcard : Fintype.card V = 7)
    {c d e : (Gᶜ).ConnectedComponent} (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc2 : c.supp.ncard = 2) (hd2 : d.supp.ncard = 2) (he3 : e.supp.ncard = 3)
    (hunion : c.supp ∪ d.supp ∪ e.supp = Set.univ)
    {u₁ v₁ : V} {p : (Gᶜ).Walk u₁ v₁} (hp : p.IsPath) (hpverts : p.toSubgraph.verts = c.supp)
    {u₂ v₂ : V} {q : (Gᶜ).Walk u₂ v₂} (hq : q.IsPath) (hqverts : q.toSubgraph.verts = d.supp)
    {x : V} {r : (Gᶜ).Walk x x} (hr : r.IsCycle) (hrverts : r.toSubgraph.verts = e.supp) :
    G.Colorable 3 := by
  classical
  have hdisj_cd : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hcd
  have hdisj_ce : Disjoint c.supp e.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hce
  have hdisj_de : Disjoint d.supp e.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := Gᶜ)) hde
  have hcover :
      ∀ y : V, y ∈ c.supp ∨ y ∈ d.supp ∨ y ∈ e.supp := by
    intro y
    have hyunion : y ∈ c.supp ∪ d.supp ∪ e.supp := by rw [hunion]; simp
    rcases hyunion with hycd | hye
    · rcases hycd with hyc | hyd
      · exact Or.inl hyc
      · exact Or.inr <| Or.inl hyd
    · exact Or.inr <| Or.inr hye
  let color : V → Fin 3 := fun y =>
    if y ∈ e.supp then 0 else if y ∈ c.supp then 1 else 2
  have hcolor_e {y : V} (hy : y ∈ e.supp) : color y = 0 := by
    unfold color
    rw [if_pos hy]
  have hcolor_c {y : V} (hy : y ∈ c.supp) : color y = 1 := by
    have hy_not_e : y ∉ e.supp := Set.disjoint_left.mp hdisj_ce hy
    unfold color
    rw [if_neg hy_not_e, if_pos hy]
  have hcolor_d {y : V} (hy : y ∈ d.supp) : color y = 2 := by
    have hy_not_e : y ∉ e.supp := Set.disjoint_left.mp hdisj_de hy
    have hy_not_c : y ∉ c.supp := Set.disjoint_right.mp hdisj_cd hy
    unfold color
    rw [if_neg hy_not_e, if_neg hy_not_c]
  have bucket0 {y : V} (hy : color y = 0) : y ∈ e.supp := by
    by_cases hye : y ∈ e.supp
    · exact hye
    · rcases hcover y with hyc | hyd | hye'
      · have : False := by simpa [hcolor_c hyc] using hy
        exact False.elim this
      · have : False := by simpa [hcolor_d hyd] using hy
        exact False.elim this
      · contradiction
  have bucket1 {y : V} (hy : color y = 1) : y ∈ c.supp := by
    rcases hcover y with hyc | hyd | hye
    · exact hyc
    · have : False := by simpa [hcolor_d hyd] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_e hye] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y ∈ d.supp := by
    rcases hcover y with hyc | hyd | hye
    · have : False := by simpa [hcolor_c hyc] using hy
      exact False.elim this
    · exact hyd
    · have : False := by simpa [hcolor_e hye] using hy
      exact False.elim this
  have hcolor : G.Coloring (Fin 3) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      exact
        ((SimpleGraph.compl_adj G y z).1
          (adj_of_mem_cycle_component_card_three
            (G := G) he3 hr hrverts (bucket0 hy0) (bucket0 hz0) (G.ne_of_adj hyz))).2 hyz
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        exact
          ((SimpleGraph.compl_adj G y z).1
            (adj_of_mem_path_component_card_two
              (G := G) hc2 hp hpverts (bucket1 hy1) (bucket1 hz1) (G.ne_of_adj hyz))).2 hyz
      · have hy2 : color y = 2 := by
          rcases hcover y with hyc | hyd | hye
          · exact False.elim (hy1 (hcolor_c hyc))
          · exact hcolor_d hyd
          · exact False.elim (hy0 (hcolor_e hye))
        have hz2 : color z = 2 := by rw [← hyzEq, hy2]
        exact
          ((SimpleGraph.compl_adj G y z).1
            (adj_of_mem_path_component_card_two
              (G := G) hd2 hq hqverts (bucket2 hy2) (bucket2 hz2) (G.ne_of_adj hyz))).2 hyz
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The seven-vertex `16`-edge degree-count profile `(3,4,0)` is explicitly `4`-colorable.

Source: exact complement-shape split `P₂ ⊔ P₅ ∨ P₃ ⊔ P₄ ∨ P₂ ⊔ P₂ ⊔ C₃`, followed by explicit
colorings of those three shapes. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_profile_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    G.Colorable 4 := by
  classical
  rcases h.compl_path_path_cycle_case_split_of_profile_three_four_zero hcard hedge hprof with
    h25 | h34 | h223
  · rcases h25 with
      ⟨c, d, hcd, hc2, hd5, hunion, u₁, v₁, _huv₁, p, hp, hpverts, u₂, v₂, _huv₂, q, hq,
        hqverts⟩
    exact
      colorable_four_of_compl_path_components_card_two_five
        (G := G) hcard hcd hc2 hd5 hunion hp hpverts hq hqverts
  · rcases h34 with
      ⟨c, d, hcd, hc3, hd4, hunion, u₁, v₁, _huv₁, p, hp, hpverts, u₂, v₂, _huv₂, q, hq,
        hqverts⟩
    exact
      colorable_four_of_compl_path_components_card_three_four
        (G := G) hcard hcd hc3 hd4 hunion hp hpverts hq hqverts
  · rcases h223 with
      ⟨c, d, e, hcd, hce, hde, hc2, hd2, he3, hunion, u₁, v₁, _huv₁, p, hp, hpverts, u₂, v₂,
        _huv₂, q, hq, hqverts, x, r, hr, hrverts⟩
    exact
      SimpleGraph.Colorable.mono (G := G) (show 3 ≤ 4 by decide)
        (colorable_three_of_compl_path_components_card_two_two_and_cycle_component_card_three
          (G := G) hcard hcd hce hde hc2 hd2 he3 hunion hp hpverts hq hqverts hr hrverts)

/-- The seven-vertex `16`-edge degree-count profile `(3,4,0)` cannot occur in an incidence-critical
non-`4`-colorable graph.

Source: immediate contradiction from the explicit `4`-coloring of the profile. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) := by
  intro hprof
  exact h.not_colorable
    (h.colorable_four_of_profile_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      hcard hedge hprof)

/-- After excluding `(3,4,0)` as well as the already-closed `(4,2,1)` branch, the exact
seven-vertex `16`-edge degree profile is forced to be `(5,0,2)`.

Source: the live seven-vertex `|E| = 16` frontier is now theorem-level sharp at the witness
profile. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  rcases
      h.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge with
    h340 | h502
  · exfalso
    exact
      (h.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge) h340
  · exact h502

/-- Live seven-vertex `K₅`-free degree profile after the `(3,4,0)` and `(4,2,1)` closures: only
the sharp witness profile `(5,0,2)` remains. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    h.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      hcard hedge

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift excluding the seven-vertex `16`-edge profile `(3,4,0)`. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge

/-- Vertex-critical lift of the exact sharp seven-vertex `16`-edge degree profile `(5,0,2)`. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge

/-- Vertex-critical lift of the sharp live seven-vertex `K₅`-free degree profile `(5,0,2)`. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift excluding the seven-vertex `16`-edge profile `(3,4,0)`. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift excluding the live seven-vertex `K₅`-free profile `(3,4,0)`
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_four_zero_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the exact sharp seven-vertex `16`-edge degree profile
`(5,0,2)`. -/
theorem IsMinimalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

/-- Minimal-counterexample lift of the sharp live seven-vertex `K₅`-free degree profile
`(5,0,2)`. -/
theorem IsMinimalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree

/-- Minimal-counterexample lift of the sharp live seven-vertex `K₅`-free degree profile `(5,0,2)`
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 5 ∧ d5 = 0 ∧ d6 = 2 := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_eq_five_zero_two_of_card_eq_seven_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
