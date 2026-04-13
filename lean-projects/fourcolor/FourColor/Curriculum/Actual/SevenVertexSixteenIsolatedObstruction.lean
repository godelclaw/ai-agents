import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import FourColor.Curriculum.Actual.SevenVertexSixteenIsolatedSupport
import FourColor.Curriculum.Actual.SevenVertexDisconnectedColoring

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If a vertex is isolated in the complement, it is adjacent in the original graph to every
vertex in the complement support.

Source: helper theorem for the rigid seven-vertex `|E| = 16` branch where the complement has two
isolated vertices and a five-vertex `2`-regular support. -/
theorem adj_of_compl_degree_eq_zero_of_mem_support
    {u x : V} (hu0 : Gᶜ.degree u = 0) (hx : x ∈ Gᶜ.support) :
    G.Adj u x := by
  have hu_not_mem : u ∉ Gᶜ.support :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hux : u ≠ x := by
    intro hEq
    exact hu_not_mem (hEq ▸ hx)
  have hux_comp : ¬ Gᶜ.Adj u x := by
    intro hux_comp
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨x, hux_comp⟩)
  simpa using (SimpleGraph.compl_adj Gᶜ u x).2 ⟨hux, hux_comp⟩

/-- Two isolated complement vertices together with a `2`-regular complement support on five
vertices force non-`4`-colorability.

Source: new obstruction theorem for the rigid `(5,0,2)` branch of the exact seven-vertex
`|E| = 16` frontier. The support is a single `5`-cycle in the complement, which becomes an odd
cycle in the original graph after skipping every other vertex; the two isolated complement
vertices then consume the remaining two colors in any hypothetical `4`-coloring. -/
theorem not_colorable_four_of_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two
    {u v : V} (huv : u ≠ v) (hu0 : Gᶜ.degree u = 0) (hv0 : Gᶜ.degree v = 0)
    (hsupp : Fintype.card Gᶜ.support = 5)
    (hreg : ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ¬ G.Colorable 4 := by
  classical
  let Hc : SimpleGraph Gᶜ.support := (Gᶜ).induce (Gᶜ.support)
  let H : SimpleGraph Gᶜ.support := G.induce (Gᶜ.support)
  rcases exists_cycle_covering_all_vertices_of_card_eq_five_of_isRegularOfDegree_two
      (G := Hc) hsupp hreg with ⟨x, p, hpc, hpverts⟩
  have hlen : p.length = 5 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hsupp] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := Hc) hpc hpverts)
  let a0 : Gᶜ.support := p.getVert 0
  let a1 : Gᶜ.support := p.getVert 1
  let a2 : Gᶜ.support := p.getVert 2
  let a3 : Gᶜ.support := p.getVert 3
  let a4 : Gᶜ.support := p.getVert 4
  have hget_ne :
      ∀ {m n : ℕ}, m ≤ 4 → n ≤ 4 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ p.length - 1 := by omega
    have hn' : n ≤ p.length - 1 := by omega
    exact hmn (hpc.getVert_injOn' hm' hn' hEq)
  have ha01 : a0 ≠ a1 := by
    simpa [a0, a1] using hget_ne (m := 0) (n := 1) (by decide) (by decide) (by decide)
  have ha02 : a0 ≠ a2 := by
    simpa [a0, a2] using hget_ne (m := 0) (n := 2) (by decide) (by decide) (by decide)
  have ha04 : a0 ≠ a4 := by
    simpa [a0, a4] using hget_ne (m := 0) (n := 4) (by decide) (by decide) (by decide)
  have ha03 : a0 ≠ a3 := by
    simpa [a0, a3] using hget_ne (m := 0) (n := 3) (by decide) (by decide) (by decide)
  have ha12 : a1 ≠ a2 := by
    simpa [a1, a2] using hget_ne (m := 1) (n := 2) (by decide) (by decide) (by decide)
  have ha13 : a1 ≠ a3 := by
    simpa [a1, a3] using hget_ne (m := 1) (n := 3) (by decide) (by decide) (by decide)
  have ha14 : a1 ≠ a4 := by
    simpa [a1, a4] using hget_ne (m := 1) (n := 4) (by decide) (by decide) (by decide)
  have ha23 : a2 ≠ a3 := by
    simpa [a2, a3] using hget_ne (m := 2) (n := 3) (by decide) (by decide) (by decide)
  have ha24 : a2 ≠ a4 := by
    simpa [a2, a4] using hget_ne (m := 2) (n := 4) (by decide) (by decide) (by decide)
  have ha34 : a3 ≠ a4 := by
    simpa [a3, a4] using hget_ne (m := 3) (n := 4) (by decide) (by decide) (by decide)
  have ha02ne : (a0 : V) ≠ a2 := by
    intro hEq
    exact ha02 (Subtype.ext hEq)
  have ha24ne : (a2 : V) ≠ a4 := by
    intro hEq
    exact ha24 (Subtype.ext hEq)
  have ha41ne : (a4 : V) ≠ a1 := by
    intro hEq
    exact ha14 (Subtype.ext hEq.symm)
  have ha13ne : (a1 : V) ≠ a3 := by
    intro hEq
    exact ha13 (Subtype.ext hEq)
  have ha30ne : (a3 : V) ≠ a0 := by
    intro hEq
    exact ha03 (Subtype.ext hEq.symm)
  have ha01C : Hc.Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have ha12C : Hc.Adj a1 a2 := by
    have h1 : 1 < p.length := by omega
    simpa [a1, a2] using p.adj_getVert_succ h1
  have ha23C : Hc.Adj a2 a3 := by
    have h2 : 2 < p.length := by omega
    simpa [a2, a3] using p.adj_getVert_succ h2
  have ha34C : Hc.Adj a3 a4 := by
    have h3 : 3 < p.length := by omega
    simpa [a3, a4] using p.adj_getVert_succ h3
  have ha40C : Hc.Adj a4 a0 := by
    have h4 : 4 < p.length := by omega
    have hAdj : Hc.Adj (p.getVert 4) (p.getVert p.length) := by
      simpa [hlen] using p.adj_getVert_succ h4
    simpa [a4, a0, p.getVert_zero, p.getVert_length] using hAdj
  have hneigh_two : ∀ y : Gᶜ.support, (Hc.neighborSet y).ncard = 2 := by
    intro y
    have hcard : Fintype.card ↥(Hc.neighborSet y) = 2 := by
      simpa [Hc, hreg y] using (Hc.card_neighborSet_eq_degree (v := y))
    have hcard_eq : Fintype.card ↥(Hc.neighborSet y) = (Hc.neighborSet y).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hcard
  have hsnd : p.snd = a1 := by
    simp [a1]
  have hpen : p.penultimate = a4 := by
    simp [SimpleGraph.Walk.penultimate, a4, hlen]
  have hget5 : p.getVert 5 = a0 := by
    calc
      p.getVert 5 = p.getVert p.length := by simp [hlen]
      _ = p.getVert 0 := by rw [p.getVert_length, p.getVert_zero]
      _ = a0 := rfl
  have hneigh0_sub : p.toSubgraph.neighborSet a0 = {a1, a4} := by
    simpa [a0, a1, a4, hsnd, hpen] using hpc.neighborSet_toSubgraph_endpoint
  have hneigh1_sub : p.toSubgraph.neighborSet a1 = {a0, a2} := by
    simpa [a0, a1, a2] using
      hpc.neighborSet_toSubgraph_internal (i := 1) (by decide) (by omega)
  have hneigh2_sub : p.toSubgraph.neighborSet a2 = {a1, a3} := by
    simpa [a1, a2, a3] using
      hpc.neighborSet_toSubgraph_internal (i := 2) (by decide) (by omega)
  have hneigh3_sub : p.toSubgraph.neighborSet a3 = {a2, a4} := by
    simpa [a2, a3, a4] using
      hpc.neighborSet_toSubgraph_internal (i := 3) (by decide) (by omega)
  have hneigh4_sub : p.toSubgraph.neighborSet a4 = {a3, a0} := by
    simpa [a0, a3, a4, hget5] using
      hpc.neighborSet_toSubgraph_internal (i := 4) (by decide) (by omega)
  have hneigh0 : Hc.neighborSet a0 = {a1, a4} := by
    have hEq :
        p.toSubgraph.neighborSet a0 = Hc.neighborSet a0 :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a0) (by
        rw [hneigh0_sub, hneigh_two a0]
        simp [ha14])
    exact hEq.symm.trans hneigh0_sub
  have hneigh1 : Hc.neighborSet a1 = {a0, a2} := by
    have hEq :
        p.toSubgraph.neighborSet a1 = Hc.neighborSet a1 :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a1) (by
        rw [hneigh1_sub, hneigh_two a1]
        simp [ha02])
    exact hEq.symm.trans hneigh1_sub
  have hneigh2 : Hc.neighborSet a2 = {a1, a3} := by
    have hEq :
        p.toSubgraph.neighborSet a2 = Hc.neighborSet a2 :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a2) (by
        rw [hneigh2_sub, hneigh_two a2]
        simp [ha13])
    exact hEq.symm.trans hneigh2_sub
  have hneigh3 : Hc.neighborSet a3 = {a2, a4} := by
    have hEq :
        p.toSubgraph.neighborSet a3 = Hc.neighborSet a3 :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a3) (by
        rw [hneigh3_sub, hneigh_two a3]
        simp [ha24])
    exact hEq.symm.trans hneigh3_sub
  have hneigh4 : Hc.neighborSet a4 = {a3, a0} := by
    have hEq :
        p.toSubgraph.neighborSet a4 = Hc.neighborSet a4 :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a4) (by
        rw [hneigh4_sub, hneigh_two a4]
        rw [Set.ncard_pair ha03.symm])
    exact hEq.symm.trans hneigh4_sub
  have hnot02C : ¬ Hc.Adj a0 a2 := by
    intro hComp
    have hmem : a2 ∈ Hc.neighborSet a0 := by
      simpa [SimpleGraph.mem_neighborSet] using hComp
    rw [hneigh0] at hmem
    rcases hmem with h | h
    · exact ha12 h.symm
    · exact ha24 h
  have hnot24C : ¬ Hc.Adj a2 a4 := by
    intro hComp
    have hmem : a4 ∈ Hc.neighborSet a2 := by
      simpa [SimpleGraph.mem_neighborSet] using hComp
    rw [hneigh2] at hmem
    rcases hmem with h | h
    · exact ha14 h.symm
    · exact ha34 h.symm
  have hnot41C : ¬ Hc.Adj a4 a1 := by
    intro hComp
    have hmem : a1 ∈ Hc.neighborSet a4 := by
      simpa [SimpleGraph.mem_neighborSet] using hComp
    rw [hneigh4] at hmem
    rcases hmem with h | h
    · exact ha13 h
    · exact ha01 h.symm
  have hnot13C : ¬ Hc.Adj a1 a3 := by
    intro hComp
    have hmem : a3 ∈ Hc.neighborSet a1 := by
      simpa [SimpleGraph.mem_neighborSet] using hComp
    rw [hneigh1] at hmem
    rcases hmem with h | h
    · exact ha03 h.symm
    · exact ha23 h.symm
  have hnot30C : ¬ Hc.Adj a3 a0 := by
    intro hComp
    have hmem : a0 ∈ Hc.neighborSet a3 := by
      simpa [SimpleGraph.mem_neighborSet] using hComp
    rw [hneigh3] at hmem
    rcases hmem with h | h
    · exact ha02 h
    · exact ha04 h
  have hG02 : H.Adj a0 a2 := by
    change G.Adj (a0 : V) (a2 : V)
    simpa using
      (SimpleGraph.compl_adj Gᶜ (a0 : V) (a2 : V)).2 ⟨ha02ne, fun hComp => hnot02C hComp⟩
  have hG24 : H.Adj a2 a4 := by
    change G.Adj (a2 : V) (a4 : V)
    simpa using
      (SimpleGraph.compl_adj Gᶜ (a2 : V) (a4 : V)).2 ⟨ha24ne, fun hComp => hnot24C hComp⟩
  have hG41 : H.Adj a4 a1 := by
    change G.Adj (a4 : V) (a1 : V)
    simpa using
      (SimpleGraph.compl_adj Gᶜ (a4 : V) (a1 : V)).2 ⟨ha41ne, fun hComp => hnot41C hComp⟩
  have hG13 : H.Adj a1 a3 := by
    change G.Adj (a1 : V) (a3 : V)
    simpa using
      (SimpleGraph.compl_adj Gᶜ (a1 : V) (a3 : V)).2 ⟨ha13ne, fun hComp => hnot13C hComp⟩
  have hG30 : H.Adj a3 a0 := by
    change G.Adj (a3 : V) (a0 : V)
    simpa using
      (SimpleGraph.compl_adj Gᶜ (a3 : V) (a0 : V)).2 ⟨ha30ne, fun hComp => hnot30C hComp⟩
  let q : H.Walk a0 a0 :=
    SimpleGraph.Walk.cons hG02
      (SimpleGraph.Walk.cons hG24
        (SimpleGraph.Walk.cons hG41
          (SimpleGraph.Walk.cons hG13
            (SimpleGraph.Walk.cons hG30 SimpleGraph.Walk.nil))))
  have hqOdd : Odd q.length := by
    simpa [q] using (show Odd 5 by decide)
  intro hcol
  let C : G.Coloring (Fin 4) := hcol.some
  have hu_not_mem : u ∉ Gᶜ.support :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have huvG : G.Adj u v := by
    have huv_comp : ¬ Gᶜ.Adj u v := by
      intro huv_comp
      exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨v, huv_comp⟩)
    simpa using (SimpleGraph.compl_adj Gᶜ u v).2 ⟨huv, huv_comp⟩
  have hcuv : C u ≠ C v := C.valid huvG
  let T : Type := { c : Fin 4 // ¬ (c = C u ∨ c = C v) }
  have hTcard : Fintype.card T = 2 := by
    calc
      Fintype.card T
          = Fintype.card {c : Fin 4 // ¬ (c = C u ∨ c = C v)} := rfl
      _ = Fintype.card (Fin 4) - Fintype.card {c : Fin 4 // c = C u ∨ c = C v} := by
          simpa using (Fintype.card_subtype_compl fun c : Fin 4 => c = C u ∨ c = C v)
      _ = 4 - 2 := by
          rw [Fintype.card_fin, Fintype.card_subtype_eq_or_eq_of_ne hcuv]
      _ = 2 := by decide
  let Dcolor : Gᶜ.support → T := fun y =>
    ⟨C y, by
      have huy : G.Adj u y := adj_of_compl_degree_eq_zero_of_mem_support (G := G) hu0 y.property
      have hvy : G.Adj v y := adj_of_compl_degree_eq_zero_of_mem_support (G := G) hv0 y.property
      intro hybad
      rcases hybad with hyu | hyv
      · exact (C.valid huy) hyu.symm
      · exact (C.valid hvy) hyv.symm⟩
  let D : H.Coloring T :=
    SimpleGraph.Coloring.mk Dcolor (by
      intro y z hyz hEq
      exact C.valid hyz (congrArg Subtype.val hEq))
  have hHcol : H.Colorable 2 := by
    simpa [hTcard] using D.colorable
  have hχge : 3 ≤ H.chromaticNumber := SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop q hqOdd
  have hχle : H.chromaticNumber ≤ 2 := hHcol.chromaticNumber_le
  have hbad : ((3 : ℕ) : ℕ∞) ≤ 2 := le_trans hχge hχle
  exact (Nat.not_succ_le_self 2) (ENat.coe_le_coe.mp hbad)

/-- Existential wrapper for the rigid `(5,0,2)` complement branch.

Source: packaging theorem for later case splits that expose the branch as two isolated complement
vertices and a five-vertex `2`-regular support. -/
theorem not_colorable_four_of_exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two
    (hcase :
      ∃ u v : V, u ≠ v ∧
        Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        Fintype.card Gᶜ.support = 5 ∧
        ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) :
    ¬ G.Colorable 4 := by
  rcases hcase with ⟨u, v, huv, hu0, hv0, hsupp, hreg⟩
  exact
    not_colorable_four_of_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two
      huv hu0 hv0 hsupp hreg

end Generic

end FourColor.Curriculum.Actual
