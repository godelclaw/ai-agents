import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexSeventeenProfileTwoFourOne
import FourColor.Curriculum.Actual.SevenVertexCycleCases
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointRealization
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointDisconnectedColoring

namespace FourColor.Curriculum.Actual

section GenericTriangle

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- A `2`-regular graph on three vertices is complete.

Source: helper theorem for the last seven-vertex `|E| = 17` profile `(3,2,2)`, used to turn the
remaining disconnected complement support branch into an explicit triangle. -/
theorem adj_of_card_eq_three_of_isRegularOfDegree_two
    (hcard : Fintype.card W = 3) (hreg : H.IsRegularOfDegree 2) {a b : W} (hab : a ≠ b) :
    H.Adj a b := by
  have hother_card :
      Fintype.card ↥((({a} : Set W)ᶜ)) = 2 := by
    calc
      Fintype.card ↥((({a} : Set W)ᶜ)) = Fintype.card W - Fintype.card ({a} : Set W) := by
        simpa using (Fintype.card_compl_set ({a} : Set W))
      _ = 3 - 1 := by rw [hcard]; simp
      _ = 2 := by decide
  have hother_ncard :
      (({a} : Set W)ᶜ).ncard = 2 := by
    have hcard_eq : Fintype.card ↥((({a} : Set W)ᶜ)) = (({a} : Set W)ᶜ).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hother_card
  have hneigh_ncard : (H.neighborSet a).ncard = 2 := by
    have hneigh_card : Fintype.card ↥(H.neighborSet a) = 2 := by
      simpa [hreg a] using (H.card_neighborSet_eq_degree (v := a))
    have hcard_eq : Fintype.card ↥(H.neighborSet a) = (H.neighborSet a).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hneigh_card
  have hsubset : H.neighborSet a ⊆ (({a} : Set W)ᶜ) := by
    intro x hx
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hax : H.Adj a x := by
      simpa [SimpleGraph.mem_neighborSet] using hx
    exact H.ne_of_adj hax.symm
  have hEq :
      H.neighborSet a = (({a} : Set W)ᶜ) := by
    apply Set.eq_of_subset_of_ncard_le hsubset
    simpa [hneigh_ncard] using hother_ncard.le
  have hbmem : b ∈ (({a} : Set W)ᶜ) := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hab
  have : b ∈ H.neighborSet a := by rw [hEq]; exact hbmem
  simpa [SimpleGraph.mem_neighborSet] using this

end GenericTriangle

section GenericSupportPath

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- If a finite graph has two isolated vertices, two degree-`1` vertices, and every other vertex
degree `2`, then connectedness of the support induces a path covering the whole support.

Source: helper theorem for the connected support half of the last seven-vertex `|E| = 17` profile
`(3,2,2)`. -/
theorem exists_path_covering_support_of_connected_induce_support_of_distinct_degree_zero_zero_degree_one_one_and_forall_degree_two_else
    {z₁ z₂ u v : W}
    (hz₁z₂ : z₁ ≠ z₂) (hz₁u : z₁ ≠ u) (hz₁v : z₁ ≠ v) (hz₂u : z₂ ≠ u) (hz₂v : z₂ ≠ v)
    (huv : u ≠ v)
    (hz₁0 : H.degree z₁ = 0) (hz₂0 : H.degree z₂ = 0)
    (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest :
      ∀ w : W, w ≠ z₁ → w ≠ z₂ → w ≠ u → w ≠ v → H.degree w = 2)
    (hconn : (H.induce H.support).Connected) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = H.support := by
  classical
  have hz₁_not_mem : z₁ ∉ H.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := H) (v := z₁)).mp hz₁0
  have hz₂_not_mem : z₂ ∉ H.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := H) (v := z₂)).mp hz₂0
  have hu_mem : u ∈ H.support := by
    exact (H.degree_pos_iff_mem_support u).1 (by simp [hu1])
  have hv_mem : v ∈ H.support := by
    exact (H.degree_pos_iff_mem_support v).1 (by simp [hv1])
  let K : SimpleGraph H.support := H.induce H.support
  have huK1 : K.degree ⟨u, hu_mem⟩ = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hu1
  have hvK1 : K.degree ⟨v, hv_mem⟩ = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hv1
  have hrestK :
      ∀ w : H.support, w ≠ ⟨u, hu_mem⟩ → w ≠ ⟨v, hv_mem⟩ → K.degree w = 2 := by
    intro w hwu hwv
    rw [SimpleGraph.degree_induce_support]
    have hwz₁ : (w : W) ≠ z₁ := by
      intro hEq
      exact hz₁_not_mem (hEq ▸ w.property)
    have hwz₂ : (w : W) ≠ z₂ := by
      intro hEq
      exact hz₂_not_mem (hEq ▸ w.property)
    exact hrest w hwz₁ hwz₂
      (fun h => hwu (Subtype.ext h))
      (fun h => hwv (Subtype.ext h))
  rcases
      exists_path_covering_all_vertices_of_connected_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := K) hconn
        (by exact fun h => huv (Subtype.ext_iff.mp h))
        huK1 hvK1 hrestK with
    ⟨p, hp, hpverts⟩
  let φ : K →g H :=
    { toFun := fun x => x.1
      map_rel' := by
        intro a b hab
        exact hab }
  refine ⟨p.map φ, SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp, ?_⟩
  ext w
  constructor
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map] at hw
    rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
    exact x.property
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map]
    refine List.mem_map.mpr ?_
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpverts]
    simp

end GenericSupportPath

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The `(3,2,2)` degree-count profile in the seven-vertex `|E| = 17` branch gives two isolated
complement vertices, two complement degree-`1` vertices, and three complement degree-`2`
vertices.

Source: new theorem translating the final remaining seven-vertex `17`-edge profile into raw
complement geometry. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_compl_degree_zero_zero_one_one_forall_rest_degree_two_of_profile_three_two_two
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 4).card
      let d5 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 5).card
      let d6 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 6).card
      d4 = 3 ∧ d5 = 2 ∧ d6 = 2) :
    ∃ z₁ z₂ u v : V,
      z₁ ≠ z₂ ∧ z₁ ≠ u ∧ z₁ ≠ v ∧ z₂ ≠ u ∧ z₂ ≠ v ∧ u ≠ v ∧
      Gᶜ.degree z₁ = 0 ∧ Gᶜ.degree z₂ = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      ∀ x : V, x ≠ z₁ → x ≠ z₂ → x ≠ u → x ≠ v → Gᶜ.degree x = 2 := by
  classical
  let s5 : Finset V := Finset.univ.filter fun x : V => G.degree x = 5
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨_hd4, hd5, hd6⟩
  have hs5 : s5.card = 2 := by
    simpa [s5] using hd5
  have hs6 : s6.card = 2 := by
    simpa [s6] using hd6
  rcases Finset.card_eq_two.mp hs6 with ⟨z₁, z₂, hz₁z₂, hs6eq⟩
  rcases Finset.card_eq_two.mp hs5 with ⟨u, v, huv, hs5eq⟩
  have hz₁6 : G.degree z₁ = 6 := by
    have hzmem : z₁ ∈ s6 := by
      rw [hs6eq]
      simp
    exact (Finset.mem_filter.mp hzmem).2
  have hz₂6 : G.degree z₂ = 6 := by
    have hzmem : z₂ ∈ s6 := by
      rw [hs6eq]
      simp
    exact (Finset.mem_filter.mp hzmem).2
  have hu5 : G.degree u = 5 := by
    have humem : u ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp humem).2
  have hv5 : G.degree v = 5 := by
    have hvmem : v ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp hvmem).2
  have hz₁u : z₁ ≠ u := by
    intro hEq
    subst u
    omega
  have hz₁v : z₁ ≠ v := by
    intro hEq
    subst v
    omega
  have hz₂u : z₂ ≠ u := by
    intro hEq
    subst u
    omega
  have hz₂v : z₂ ≠ v := by
    intro hEq
    subst v
    omega
  have hrest4 : ∀ x : V, x ≠ z₁ → x ≠ z₂ → x ≠ u → x ≠ v → G.degree x = 4 := by
    intro x hxz₁ hxz₂ hxu hxv
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
        hcard hedge x with hx4 | hx5 | hx6
    · exact hx4
    · have hxmem : x ∈ s5 := by
        simp [s5, hx5]
      rw [hs5eq] at hxmem
      simp [hxu, hxv] at hxmem
    · have hxmem : x ∈ s6 := by
        simp [s6, hx6]
      rw [hs6eq] at hxmem
      simp [hxz₁, hxz₂] at hxmem
  have hz₁0 : Gᶜ.degree z₁ = 0 := by
    simpa [hcard, hz₁6] using (SimpleGraph.degree_compl (G := G) (v := z₁))
  have hz₂0 : Gᶜ.degree z₂ = 0 := by
    simpa [hcard, hz₂6] using (SimpleGraph.degree_compl (G := G) (v := z₂))
  have hu1 : Gᶜ.degree u = 1 := by
    simpa [hcard, hu5] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hv1 : Gᶜ.degree v = 1 := by
    simpa [hcard, hv5] using (SimpleGraph.degree_compl (G := G) (v := v))
  have hrest2 : ∀ x : V, x ≠ z₁ → x ≠ z₂ → x ≠ u → x ≠ v → Gᶜ.degree x = 2 := by
    intro x hxz₁ hxz₂ hxu hxv
    simpa [hcard, hrest4 x hxz₁ hxz₂ hxu hxv] using (SimpleGraph.degree_compl (G := G) (v := x))
  exact ⟨z₁, z₂, u, v, hz₁z₂, hz₁u, hz₁v, hz₂u, hz₂v, huv, hz₁0, hz₂0, hu1, hv1, hrest2⟩

/-- In the final seven-vertex `17`-edge profile, connected complement support forces a `5`-clique
in the original graph.

Source: the connected support is a `P₅`; alternating path vertices together with the two isolated
complement vertices form a concrete `K₅`. -/
theorem not_cliqueFree_of_compl_zero_zero_one_one_profile_of_connected_support
    (hcard : Fintype.card V = 7)
    {z₁ z₂ u v : V}
    (hz₁z₂ : z₁ ≠ z₂) (hz₁u : z₁ ≠ u) (hz₁v : z₁ ≠ v) (hz₂u : z₂ ≠ u) (hz₂v : z₂ ≠ v)
    (huv : u ≠ v)
    (hz₁0 : Gᶜ.degree z₁ = 0) (hz₂0 : Gᶜ.degree z₂ = 0)
    (hu1 : Gᶜ.degree u = 1) (hv1 : Gᶜ.degree v = 1)
    (hrest :
      ∀ x : V, x ≠ z₁ → x ≠ z₂ → x ≠ u → x ≠ v → Gᶜ.degree x = 2)
    (hconn : ((Gᶜ).induce (Gᶜ.support)).Connected) :
    ¬ G.CliqueFree 5 := by
  classical
  have hz₁_not_mem : z₁ ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z₁)).mp hz₁0
  have hz₂_not_mem : z₂ ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z₂)).mp hz₂0
  have hcard_support : Fintype.card Gᶜ.support = 5 := by
    have hsupport_eq : Gᶜ.support = ({z₁, z₂} : Set V)ᶜ := by
      ext x
      constructor
      · intro hx
        have hxz₁ : x ≠ z₁ := by
          intro hEq
          exact hz₁_not_mem (hEq ▸ hx)
        have hxz₂ : x ≠ z₂ := by
          intro hEq
          exact hz₂_not_mem (hEq ▸ hx)
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxz₁, hxz₂]
      · intro hx
        have hxz₁ : x ≠ z₁ := by
          simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          exact hx.1
        have hxz₂ : x ≠ z₂ := by
          simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          exact hx.2
        by_cases hxu : x = u
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            simp [hu1])
        by_cases hxv : x = v
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            simp [hv1])
        exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hrest x hxz₁ hxz₂ hxu hxv])
    have hpair_card : Fintype.card ({z₁, z₂} : Set V) = 2 := by
      rw [← Set.toFinset_card]
      simp [hz₁z₂]
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({z₁, z₂} : Set V) := by
        simpa [hsupport_eq] using (Fintype.card_compl_set ({z₁, z₂} : Set V))
      _ = 7 - 2 := by rw [hcard, hpair_card]
      _ = 5 := by decide
  rcases
      exists_path_covering_support_of_connected_induce_support_of_distinct_degree_zero_zero_degree_one_one_and_forall_degree_two_else
        (H := Gᶜ) hz₁z₂ hz₁u hz₁v hz₂u hz₂v huv hz₁0 hz₂0 hu1 hv1 hrest hconn with
    ⟨p, hp, hpverts⟩
  have hsupp_ncard : Gᶜ.support.ncard = 5 := by
    have hcard_eq : Gᶜ.support.ncard = Fintype.card Gᶜ.support := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hcard_eq.trans hcard_support
  have hlen : p.length = 4 := by
    simpa [hpverts, hsupp_ncard] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := Gᶜ) hp hpverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let a3 : V := p.getVert 3
  let a4 : V := p.getVert 4
  have ha0 : a0 = u := by
    simpa [a0] using p.getVert_zero
  have ha4 : a4 = v := by
    calc
      a4 = p.getVert p.length := by simpa [a4, hlen]
      _ = v := by rw [p.getVert_length]
  have hget_ne :
      ∀ {m n : ℕ}, m ≤ 4 → n ≤ 4 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    apply hmn
    exact hp.getVert_injOn (by simpa [hlen] using hm) (by simpa [hlen] using hn) hEq
  have ha20 : a2 ≠ a0 := by
    simpa [a2, a0] using hget_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have ha21 : a2 ≠ a1 := by
    simpa [a2, a1] using hget_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have ha40 : a4 ≠ a0 := by
    simpa [a4, a0] using hget_ne (m := 4) (n := 0) (by decide) (by decide) (by decide)
  have ha41 : a4 ≠ a1 := by
    simpa [a4, a1] using hget_ne (m := 4) (n := 1) (by decide) (by decide) (by decide)
  have ha42 : a4 ≠ a2 := by
    simpa [a4, a2] using hget_ne (m := 4) (n := 2) (by decide) (by decide) (by decide)
  have ha43 : a4 ≠ a3 := by
    simpa [a4, a3] using hget_ne (m := 4) (n := 3) (by decide) (by decide) (by decide)
  have h01 : Gᶜ.Adj a0 a1 := by
    have hlt : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ hlt
  have h34 : Gᶜ.Adj a3 a4 := by
    have hlt : 3 < p.length := by omega
    simpa [a3, a4] using p.adj_getVert_succ hlt
  have hu_unique : ∃! x : V, Gᶜ.Adj u x :=
    SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hu1
  have hv_unique : ∃! x : V, Gᶜ.Adj v x :=
    SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hv1
  have hnot02 : ¬ Gᶜ.Adj a0 a2 := by
    intro h02
    have ha2eq1 : a2 = a1 := by
      rcases hu_unique with ⟨x, hx, hxuniq⟩
      calc
        a2 = x := hxuniq a2 (ha0 ▸ h02)
        _ = a1 := by symm; exact hxuniq a1 (ha0 ▸ h01)
    exact ha21 ha2eq1
  have hnot04 : ¬ Gᶜ.Adj a0 a4 := by
    intro h04
    have ha4eq1 : a4 = a1 := by
      rcases hu_unique with ⟨x, hx, hxuniq⟩
      calc
        a4 = x := hxuniq a4 (ha0 ▸ h04)
        _ = a1 := by symm; exact hxuniq a1 (ha0 ▸ h01)
    exact ha41 ha4eq1
  have hnot24 : ¬ Gᶜ.Adj a2 a4 := by
    intro h24
    have ha2eq3 : a2 = a3 := by
      rcases hv_unique with ⟨x, hx, hxuniq⟩
      calc
        a2 = x := hxuniq a2 (ha4 ▸ h24.symm)
        _ = a3 := by symm; exact hxuniq a3 (ha4 ▸ h34.symm)
    exact hget_ne (m := 2) (n := 3) (by decide) (by decide) (by decide) ha2eq3
  have ha0mem : a0 ∈ Gᶜ.support := by
    simpa [ha0] using (Gᶜ.degree_pos_iff_mem_support u).1 (by simp [hu1])
  have ha2mem : a2 ∈ Gᶜ.support := by
    have hsupp : a2 ∈ p.support :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨2, by simp [a2], by omega⟩
    exact hpverts ▸ (p.mem_verts_toSubgraph.mpr hsupp)
  have ha4mem : a4 ∈ Gᶜ.support := by
    simpa [ha4] using (Gᶜ.degree_pos_iff_mem_support v).1 (by simp [hv1])
  have ha2z₁ : a2 ≠ z₁ := by
    intro hEq
    exact hz₁_not_mem (hEq ▸ ha2mem)
  have ha2z₂ : a2 ≠ z₂ := by
    intro hEq
    exact hz₂_not_mem (hEq ▸ ha2mem)
  have isolated_adj_z₁ {x : V} (hx : x ∈ Gᶜ.support) : G.Adj z₁ x := by
    by_contra hxG
    have hxne : z₁ ≠ x := by
      intro hEq
      exact hz₁_not_mem (hEq ▸ hx)
    have hcomp : Gᶜ.Adj z₁ x := (SimpleGraph.compl_adj G z₁ x).2 ⟨hxne, hxG⟩
    exact hz₁_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨x, hcomp⟩)
  have isolated_adj_z₂ {x : V} (hx : x ∈ Gᶜ.support) : G.Adj z₂ x := by
    by_contra hxG
    have hxne : z₂ ≠ x := by
      intro hEq
      exact hz₂_not_mem (hEq ▸ hx)
    have hcomp : Gᶜ.Adj z₂ x := (SimpleGraph.compl_adj G z₂ x).2 ⟨hxne, hxG⟩
    exact hz₂_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨x, hcomp⟩)
  have hz₁a0 : G.Adj z₁ a0 := by
    exact isolated_adj_z₁ ha0mem
  have hz₁a2 : G.Adj z₁ a2 := by
    exact isolated_adj_z₁ ha2mem
  have hz₁a4 : G.Adj z₁ a4 := by
    exact isolated_adj_z₁ ha4mem
  have hz₂a0 : G.Adj z₂ a0 := by
    exact isolated_adj_z₂ ha0mem
  have hz₂a2 : G.Adj z₂ a2 := by
    exact isolated_adj_z₂ ha2mem
  have hz₂a4 : G.Adj z₂ a4 := by
    exact isolated_adj_z₂ ha4mem
  have hz₁z₂G : G.Adj z₁ z₂ := by
    by_contra hz
    exact hz₁_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2
      ⟨z₂, (SimpleGraph.compl_adj G z₁ z₂).2 ⟨hz₁z₂, hz⟩⟩)
  have ha0a2G : G.Adj a0 a2 := by
    by_contra h
    exact hnot02 ((SimpleGraph.compl_adj G a0 a2).2 ⟨ha20.symm, h⟩)
  have ha0a4G : G.Adj a0 a4 := by
    by_contra h
    exact hnot04 ((SimpleGraph.compl_adj G a0 a4).2 ⟨ha40.symm, h⟩)
  have ha2a4G : G.Adj a2 a4 := by
    by_contra h
    exact hnot24 ((SimpleGraph.compl_adj G a2 a4).2 ⟨ha42.symm, h⟩)
  let s : Finset V := {z₁, z₂, a0, a2, a4}
  have hsClique : G.IsClique s := by
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    simp [s] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl
    all_goals
      first
        | contradiction
        | exact hz₁z₂G
        | exact hz₁z₂G.symm
        | exact hz₁a0
        | exact hz₁a0.symm
        | exact hz₁a2
        | exact hz₁a2.symm
        | exact hz₁a4
        | exact hz₁a4.symm
        | exact hz₂a0
        | exact hz₂a0.symm
        | exact hz₂a2
        | exact hz₂a2.symm
        | exact hz₂a4
        | exact hz₂a4.symm
        | exact ha0a2G
        | exact ha0a2G.symm
        | exact ha0a4G
        | exact ha0a4G.symm
        | exact ha2a4G
        | exact ha2a4G.symm
  have hsCard : s.card = 5 := by
    have ha2u : a2 ≠ u := by
      simpa [ha0] using ha20
    have ha2v : a2 ≠ v := by
      simpa [ha4] using ha42.symm
    simpa [s, ha0, ha4] using
      (show ({z₁, z₂, u, a2, v} : Finset V).card = 5 from by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa [Finset.mem_singleton] using ha2v
        · intro hu_mem
          simp at hu_mem
          rcases hu_mem with h | h
          · exact ha2u h.symm
          · exact huv h
        · intro hz₂_mem
          simp at hz₂_mem
          rcases hz₂_mem with h | h | h
          · exact hz₂u h
          · exact ha2z₂ h.symm
          · exact hz₂v h
        · intro hz₁_mem
          simp at hz₁_mem
          rcases hz₁_mem with h | h | h | h
          · exact hz₁z₂ h
          · exact hz₁u h
          · exact ha2z₁ h.symm
          · exact hz₁v h)
  have hsNClique : G.IsNClique 5 s := by
    rw [SimpleGraph.isNClique_iff]
    exact ⟨hsClique, hsCard⟩
  exact hsNClique.not_cliqueFree

/-- In the final seven-vertex `17`-edge profile, disconnected complement support is explicitly
`4`-colorable in the original graph.

Source: the disconnected support splits as an edge plus a triangle, while the two isolated
complement vertices each take their own color. -/
theorem colorable_four_of_compl_zero_zero_one_one_profile_of_not_connected_support
    (hcard : Fintype.card V = 7)
    {z₁ z₂ u v : V}
    (hz₁z₂ : z₁ ≠ z₂) (hz₁u : z₁ ≠ u) (hz₁v : z₁ ≠ v) (hz₂u : z₂ ≠ u) (hz₂v : z₂ ≠ v)
    (huv : u ≠ v)
    (hz₁0 : Gᶜ.degree z₁ = 0) (hz₂0 : Gᶜ.degree z₂ = 0)
    (hu1 : Gᶜ.degree u = 1) (hv1 : Gᶜ.degree v = 1)
    (hrest :
      ∀ x : V, x ≠ z₁ → x ≠ z₂ → x ≠ u → x ≠ v → Gᶜ.degree x = 2)
    (hnotconn : ¬ ((Gᶜ).induce (Gᶜ.support)).Connected) :
    G.Colorable 4 := by
  classical
  have hz₁_not_mem : z₁ ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z₁)).mp hz₁0
  have hz₂_not_mem : z₂ ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z₂)).mp hz₂0
  have hu_mem : u ∈ Gᶜ.support := by
    exact (Gᶜ.degree_pos_iff_mem_support u).1 (by simp [hu1])
  have hv_mem : v ∈ Gᶜ.support := by
    exact (Gᶜ.degree_pos_iff_mem_support v).1 (by simp [hv1])
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
  have huH1 : H.degree ⟨u, hu_mem⟩ = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hu1
  have hvH1 : H.degree ⟨v, hv_mem⟩ = 1 := by
    rw [SimpleGraph.degree_induce_support]
    exact hv1
  have hrestH :
      ∀ w : Gᶜ.support, w ≠ ⟨u, hu_mem⟩ → w ≠ ⟨v, hv_mem⟩ → H.degree w = 2 := by
    intro w hwu hwv
    rw [SimpleGraph.degree_induce_support]
    have hwz₁ : (w : V) ≠ z₁ := by
      intro hEq
      exact hz₁_not_mem (hEq ▸ w.property)
    have hwz₂ : (w : V) ≠ z₂ := by
      intro hEq
      exact hz₂_not_mem (hEq ▸ w.property)
    exact hrest w hwz₁ hwz₂
      (fun h => hwu (Subtype.ext h))
      (fun h => hwv (Subtype.ext h))
  have hreach :
      H.Reachable ⟨u, hu_mem⟩ ⟨v, hv_mem⟩ :=
    reachable_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
      (H := H) (by exact fun h => huv (Subtype.ext_iff.mp h)) huH1 hvH1 hrestH
  let c : H.ConnectedComponent := H.connectedComponentMk ⟨u, hu_mem⟩
  have hu_c : ⟨u, hu_mem⟩ ∈ c.supp := by
    simpa [c] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := ⟨u, hu_mem⟩))
  have hv_c : ⟨v, hv_mem⟩ ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [c] using hreach.symm
  have hc_ne_univ : c.supp ≠ Set.univ := by
    intro hEq
    have hc_card : c.supp.ncard = Fintype.card Gᶜ.support := by
      simpa [hEq, Set.ncard_univ, Nat.card_eq_fintype_card]
    exact hnotconn (connected_of_connectedComponent_ncard_eq_card (G := H) c hc_card)
  have hcard_support : Fintype.card Gᶜ.support = 5 := by
    have hsupport_eq : Gᶜ.support = ({z₁, z₂} : Set V)ᶜ := by
      ext x
      constructor
      · intro hx
        have hxz₁ : x ≠ z₁ := by
          intro hEq
          exact hz₁_not_mem (hEq ▸ hx)
        have hxz₂ : x ≠ z₂ := by
          intro hEq
          exact hz₂_not_mem (hEq ▸ hx)
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxz₁, hxz₂]
      · intro hx
        have hxz₁ : x ≠ z₁ := by
          simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          exact hx.1
        have hxz₂ : x ≠ z₂ := by
          simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          exact hx.2
        by_cases hxu : x = u
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            simp [hu1])
        by_cases hxv : x = v
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            simp [hv1])
        exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hrest x hxz₁ hxz₂ hxu hxv])
    have hpair_card : Fintype.card ({z₁, z₂} : Set V) = 2 := by
      rw [← Set.toFinset_card]
      simp [hz₁z₂]
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({z₁, z₂} : Set V) := by
        simpa [hsupport_eq] using (Fintype.card_compl_set ({z₁, z₂} : Set V))
      _ = 7 - 2 := by rw [hcard, hpair_card]
      _ = 5 := by decide
  have hc_lt : c.supp.ncard < (Set.univ : Set Gᶜ.support).ncard := by
    have hsubset : c.supp ⊆ (Set.univ : Set Gᶜ.support) := by
      intro x hx
      simp
    have hle : c.supp.ncard ≤ (Set.univ : Set Gᶜ.support).ncard := Set.ncard_le_ncard hsubset
    by_contra hnotlt
    have hEqCard : c.supp.ncard = (Set.univ : Set Gᶜ.support).ncard :=
      Nat.le_antisymm hle (Nat.not_lt.mp hnotlt)
    have hEq : c.supp = (Set.univ : Set Gᶜ.support) := by
      apply Set.eq_of_subset_of_ncard_le hsubset
      simpa [hEqCard]
    exact hc_ne_univ hEq
  obtain ⟨w, _, hw_not_c⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hc_lt
  let d : H.ConnectedComponent := H.connectedComponentMk w
  have hw_d : w ∈ d.supp := by
    simpa [d] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := w))
  have hcd : d ≠ c := by
    intro hEq
    exact hw_not_c (hEq ▸ hw_d)
  have hdisj : Disjoint c.supp d.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := H)) hcd.symm
  have hddeg : ∀ x : Gᶜ.support, x ∈ d.supp → H.degree x = 2 := by
    intro x hx
    have hxu : x ≠ ⟨u, hu_mem⟩ := by
      intro hEq
      exact Set.disjoint_left.mp hdisj (hEq ▸ hu_c) hx
    have hxv : x ≠ ⟨v, hv_mem⟩ := by
      intro hEq
      exact Set.disjoint_left.mp hdisj (hEq ▸ hv_c) hx
    exact hrestH x hxu hxv
  have hdge3 : 3 ≤ d.supp.ncard :=
    connectedComponent_ncard_ge_three_of_forall_degree_eq_two (H := H) d hddeg
  have hcge2 : 2 ≤ c.supp.ncard := by
    have hgt : 1 < c.supp.ncard := by
      exact (Set.one_lt_ncard).2 ⟨⟨u, hu_mem⟩, hu_c, ⟨v, hv_mem⟩, hv_c, by
        exact fun h => huv (Subtype.ext_iff.mp h)⟩
    omega
  have hdsubset : d.supp ⊆ (Set.univ : Set Gᶜ.support) \ c.supp := by
    intro x hx
    refine ⟨by simp, ?_⟩
    intro hxc
    exact Set.disjoint_left.mp hdisj hxc hx
  have hdle3 : d.supp.ncard ≤ 3 := by
    calc
      d.supp.ncard ≤ ((Set.univ : Set Gᶜ.support) \ c.supp).ncard := Set.ncard_le_ncard hdsubset
      _ = 5 - c.supp.ncard := by
        rw [Set.ncard_diff (show c.supp ⊆ (Set.univ : Set Gᶜ.support) by
          intro x hx
          simp)]
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard_support]
      _ ≤ 3 := by omega
  have hd3 : d.supp.ncard = 3 := by omega
  have hcsubset : c.supp ⊆ (Set.univ : Set Gᶜ.support) \ d.supp := by
    intro x hx
    refine ⟨by simp, ?_⟩
    intro hxd
    exact Set.disjoint_left.mp hdisj hx hxd
  have hcle2 : c.supp.ncard ≤ 2 := by
    calc
      c.supp.ncard ≤ ((Set.univ : Set Gᶜ.support) \ d.supp).ncard := Set.ncard_le_ncard hcsubset
      _ = 5 - d.supp.ncard := by
        rw [Set.ncard_diff (show d.supp ⊆ (Set.univ : Set Gᶜ.support) by
          intro x hx
          simp)]
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard_support]
      _ = 2 := by simp [hd3]
  have hc2 : c.supp.ncard = 2 := by omega
  have hcuv_eq : c.supp = {⟨u, hu_mem⟩, ⟨v, hv_mem⟩} := by
    apply Set.eq_of_subset_of_ncard_le
    · intro x hx
      have hx_cases : x = ⟨u, hu_mem⟩ ∨ x = ⟨v, hv_mem⟩ := by
        have hsmall :
            ({⟨u, hu_mem⟩, ⟨v, hv_mem⟩} : Set Gᶜ.support).ncard = c.supp.ncard := by
          simp [huv, hc2]
        have hsubset :
            ({⟨u, hu_mem⟩, ⟨v, hv_mem⟩} : Set Gᶜ.support) ⊆ c.supp := by
          intro y hy
          simp at hy
          rcases hy with rfl | rfl
          · exact hu_c
          · exact hv_c
        have hEqSmall :
            ({⟨u, hu_mem⟩, ⟨v, hv_mem⟩} : Set Gᶜ.support) = c.supp := by
          apply Set.eq_of_subset_of_ncard_le hsubset
          simpa [hsmall]
        have : x ∈ ({⟨u, hu_mem⟩, ⟨v, hv_mem⟩} : Set Gᶜ.support) := by
          rw [hEqSmall]
          exact hx
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx_cases
    · simp [huv, hc2]
    · simp
  have hunion : c.supp ∪ d.supp = Set.univ := by
    have hsubset : c.supp ∪ d.supp ⊆ (Set.univ : Set Gᶜ.support) := by
      intro x hx
      simp
    have hcard_le : (Set.univ : Set Gᶜ.support).ncard ≤ (c.supp ∪ d.supp).ncard := by
      have hcard_union : (c.supp ∪ d.supp).ncard = 5 := by
        rw [Set.ncard_union_eq hdisj]
        omega
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard_support, hcard_union]
    exact Set.eq_of_subset_of_ncard_le hsubset hcard_le
  rcases
      exists_path_covering_endpoint_connectedComponent_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := H) (by exact fun h => huv (Subtype.ext_iff.mp h)) huH1 hvH1 hrestH with
    ⟨p, hp, hpverts⟩
  have hlenp : p.length = 1 := by
    simpa [hpverts, c, hc2] using
      (SimpleGraph.Walk.IsPath.length_eq_ncard_of_toSubgraph_verts_eq (G := H) hp hpverts)
  have huvH : H.Adj ⟨u, hu_mem⟩ ⟨v, hv_mem⟩ := by
    have hlt : 0 < p.length := by omega
    have h01 : H.Adj (p.getVert 0) (p.getVert 1) := by
      simpa using p.adj_getVert_succ hlt
    have h1eq : p.getVert 1 = ⟨v, hv_mem⟩ := by
      calc
        p.getVert 1 = p.getVert p.length := by simpa [hlenp]
        _ = ⟨v, hv_mem⟩ := by rw [p.getVert_length]
    simpa [p.getVert_zero, h1eq] using h01
  rcases Set.ncard_eq_three.mp hd3 with ⟨b₀, b₁, b₂, hb₀₁, hb₀₂, hb₁₂, hd_eq⟩
  let K : SimpleGraph d.supp := H.induce d.supp
  have hKcard : Fintype.card d.supp = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hd3
  have hKreg : K.IsRegularOfDegree 2 := by
    intro x
    have hdeg_eq : K.degree x = H.degree x := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := d.supp)
          (v := x)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := d) x.property))
    exact hdeg_eq.trans (hddeg x x.property)
  have hb₀mem : b₀ ∈ d.supp := by
    rw [hd_eq]
    simp
  have hb₁mem : b₁ ∈ d.supp := by
    rw [hd_eq]
    simp
  have hb₂mem : b₂ ∈ d.supp := by
    rw [hd_eq]
    simp
  have hb₀eqd : H.connectedComponentMk b₀ = d := by
    rwa [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb₀mem
  have hb₁eqd : H.connectedComponentMk b₁ = d := by
    rwa [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb₁mem
  have hb₂eqd : H.connectedComponentMk b₂ = d := by
    rwa [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb₂mem
  have hb₀₁_adj : H.Adj b₀ b₁ := by
    have : K.Adj ⟨b₀, hb₀mem⟩ ⟨b₁, hb₁mem⟩ :=
      adj_of_card_eq_three_of_isRegularOfDegree_two (H := K) hKcard hKreg
        (by
          intro h
          exact hb₀₁ (Subtype.ext_iff.mp h))
    exact this
  have hb₀₂_adj : H.Adj b₀ b₂ := by
    have : K.Adj ⟨b₀, hb₀mem⟩ ⟨b₂, hb₂mem⟩ :=
      adj_of_card_eq_three_of_isRegularOfDegree_two (H := K) hKcard hKreg
        (by
          intro h
          exact hb₀₂ (Subtype.ext_iff.mp h))
    exact this
  have hb₁₂_adj : H.Adj b₁ b₂ := by
    have : K.Adj ⟨b₁, hb₁mem⟩ ⟨b₂, hb₂mem⟩ :=
      adj_of_card_eq_three_of_isRegularOfDegree_two (H := K) hKcard hKreg
        (by
          intro h
          exact hb₁₂ (Subtype.ext_iff.mp h))
    exact this
  have huvG : ¬ G.Adj u v := by
    exact ((SimpleGraph.compl_adj G u v).1 (by simpa [H] using huvH)).2
  have hb₀₁G : ¬ G.Adj (b₀ : V) (b₁ : V) := by
    exact ((SimpleGraph.compl_adj G (b₀ : V) (b₁ : V)).1 (by simpa [H] using hb₀₁_adj)).2
  have hb₀₂G : ¬ G.Adj (b₀ : V) (b₂ : V) := by
    exact ((SimpleGraph.compl_adj G (b₀ : V) (b₂ : V)).1 (by simpa [H] using hb₀₂_adj)).2
  have hb₁₂G : ¬ G.Adj (b₁ : V) (b₂ : V) := by
    exact ((SimpleGraph.compl_adj G (b₁ : V) (b₂ : V)).1 (by simpa [H] using hb₁₂_adj)).2
  have hb₀z₁ : (b₀ : V) ≠ z₁ := by
    intro hEq
    exact hz₁_not_mem (hEq ▸ b₀.property)
  have hb₀z₂ : (b₀ : V) ≠ z₂ := by
    intro hEq
    exact hz₂_not_mem (hEq ▸ b₀.property)
  have hb₁z₁ : (b₁ : V) ≠ z₁ := by
    intro hEq
    exact hz₁_not_mem (hEq ▸ b₁.property)
  have hb₁z₂ : (b₁ : V) ≠ z₂ := by
    intro hEq
    exact hz₂_not_mem (hEq ▸ b₁.property)
  have hb₂z₁ : (b₂ : V) ≠ z₁ := by
    intro hEq
    exact hz₁_not_mem (hEq ▸ b₂.property)
  have hb₂z₂ : (b₂ : V) ≠ z₂ := by
    intro hEq
    exact hz₂_not_mem (hEq ▸ b₂.property)
  have hb₀u : (b₀ : V) ≠ u := by
    intro hEq
    have hb₀u_eq : b₀ = (⟨u, hu_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨u, hu_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₀u_eq] using hb₀eqd
    have : (⟨u, hu_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hu_c this
  have hb₀v : (b₀ : V) ≠ v := by
    intro hEq
    have hb₀v_eq : b₀ = (⟨v, hv_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨v, hv_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₀v_eq] using hb₀eqd
    have : (⟨v, hv_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hv_c this
  have hb₁u : (b₁ : V) ≠ u := by
    intro hEq
    have hb₁u_eq : b₁ = (⟨u, hu_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨u, hu_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₁u_eq] using hb₁eqd
    have : (⟨u, hu_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hu_c this
  have hb₁v : (b₁ : V) ≠ v := by
    intro hEq
    have hb₁v_eq : b₁ = (⟨v, hv_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨v, hv_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₁v_eq] using hb₁eqd
    have : (⟨v, hv_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hv_c this
  have hb₂u : (b₂ : V) ≠ u := by
    intro hEq
    have hb₂u_eq : b₂ = (⟨u, hu_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨u, hu_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₂u_eq] using hb₂eqd
    have : (⟨u, hu_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hu_c this
  have hb₂v : (b₂ : V) ≠ v := by
    intro hEq
    have hb₂v_eq : b₂ = (⟨v, hv_mem⟩ : Gᶜ.support) := Subtype.ext hEq
    have heq : H.connectedComponentMk (⟨v, hv_mem⟩ : Gᶜ.support) = d := by
      simpa [hb₂v_eq] using hb₂eqd
    have : (⟨v, hv_mem⟩ : Gᶜ.support) ∈ d.supp := by
      rwa [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Set.disjoint_left.mp hdisj hv_c this
  have hcover :
      ∀ x : V, x = z₁ ∨ x = z₂ ∨ x = u ∨ x = v ∨ x = (b₀ : V) ∨ x = (b₁ : V) ∨ x = (b₂ : V) := by
    intro x
    by_cases hxz₁ : x = z₁
    · exact Or.inl hxz₁
    by_cases hxz₂ : x = z₂
    · exact Or.inr <| Or.inl hxz₂
    have hxmem : x ∈ Gᶜ.support := by
      exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
        by_cases hxu : x = u
        · subst x
          simp [hu1]
        by_cases hxv : x = v
        · subst x
          simp [hv1]
        simpa [hrest x hxz₁ hxz₂ hxu hxv])
    let xs : Gᶜ.support := ⟨x, hxmem⟩
    have hxs : xs ∈ c.supp ∪ d.supp := by rw [hunion]; simp
    rcases hxs with hxc | hxd
    · have hxc' : xs = ⟨u, hu_mem⟩ ∨ xs = ⟨v, hv_mem⟩ := by
        have : xs ∈ ({⟨u, hu_mem⟩, ⟨v, hv_mem⟩} : Set Gᶜ.support) := by
          rw [← hcuv_eq]
          exact hxc
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      rcases hxc' with hxu | hxv
      · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext_iff.mp hxu)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext_iff.mp hxv)
    · have hxd' : xs = b₀ ∨ xs = b₁ ∨ xs = b₂ := by
        simpa [hd_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using hxd
      rcases hxd' with hxb₀ | hxb₁ | hxb₂
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext_iff.mp hxb₀)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext_iff.mp hxb₁)
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext_iff.mp hxb₂)
  let color : V → Fin 4 := fun x =>
    if x = z₁ then 0
    else if x = z₂ then 1
    else if x = u ∨ x = v then 2
    else 3
  have hcolor_z₁ : color z₁ = 0 := by simp [color]
  have hcolor_z₂ : color z₂ = 1 := by simp [color, hz₁z₂, eq_comm]
  have hcolor_u : color u = 2 := by simp [color, hz₁u, hz₂u, eq_comm]
  have hcolor_v : color v = 2 := by simp [color, hz₁v, hz₂v, huv, eq_comm]
  have hcolor_b₀ : color (b₀ : V) = 3 := by
    simp [color, hb₀z₁, hb₀z₂, hb₀u, hb₀v]
  have hcolor_b₁ : color (b₁ : V) = 3 := by
    simp [color, hb₁z₁, hb₁z₂, hb₁u, hb₁v]
  have hcolor_b₂ : color (b₂ : V) = 3 := by
    simp [color, hb₂z₁, hb₂z₂, hb₂u, hb₂v]
  have bucket0 {x : V} (hx : color x = 0) : x = z₁ := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · have : False := by simpa [hcolor_z₂] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_v] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₀] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₁] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₂] using hx
      exact False.elim this
  have bucket1 {x : V} (hx : color x = 1) : x = z₂ := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_z₁] using hx
      exact False.elim this
    · rfl
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_v] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₀] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₁] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₂] using hx
      exact False.elim this
  have bucket2 {x : V} (hx : color x = 2) : x = u ∨ x = v := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_z₁] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_z₂] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b₀] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₁] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_b₂] using hx
      exact False.elim this
  have bucket3 {x : V} (hx : color x = 3) : x = (b₀ : V) ∨ x = (b₁ : V) ∨ x = (b₂ : V) := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_z₁] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_z₂] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_u] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_v] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr rfl
  have hcoloring : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    by_cases hx0 : color x = 0
    · have hy0 : color y = 0 := by rw [← hEq, hx0]
      rw [bucket0 hx0, bucket0 hy0] at hxy
      exact G.loopless _ hxy
    · by_cases hx1 : color x = 1
      · have hy1 : color y = 1 := by rw [← hEq, hx1]
        rw [bucket1 hx1, bucket1 hy1] at hxy
        exact G.loopless _ hxy
      · by_cases hx2 : color x = 2
        · have hy2 : color y = 2 := by rw [← hEq, hx2]
          rcases bucket2 hx2 with rfl | rfl
          · rcases bucket2 hy2 with rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact huvG hxy
          · rcases bucket2 hy2 with rfl | rfl
            · exact huvG hxy.symm
            · exact (G.ne_of_adj hxy) rfl
        · have hx3 : color x = 3 := by
            rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact False.elim (hx0 hcolor_z₁)
            · exact False.elim (hx1 hcolor_z₂)
            · exact False.elim (hx2 hcolor_u)
            · exact False.elim (hx2 hcolor_v)
            · exact hcolor_b₀
            · exact hcolor_b₁
            · exact hcolor_b₂
          have hy3 : color y = 3 := by rw [← hEq, hx3]
          rcases bucket3 hx3 with rfl | rfl | rfl
          · rcases bucket3 hy3 with rfl | rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact hb₀₁G hxy
            · exact hb₀₂G hxy
          · rcases bucket3 hy3 with rfl | rfl | rfl
            · exact hb₀₁G hxy.symm
            · exact (G.ne_of_adj hxy) rfl
            · exact hb₁₂G hxy
          · rcases bucket3 hy3 with rfl | rfl | rfl
            · exact hb₀₂G hxy.symm
            · exact hb₁₂G hxy.symm
            · exact (G.ne_of_adj hxy) rfl
  exact hcoloring.colorable

/-- Under `K₅`-freeness, the last remaining seven-vertex `17`-edge profile `(3,2,2)` cannot
occur.

Source: the connected support branch forces a `K₅`, while the disconnected support branch is
explicitly `4`-colorable. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 4).card
      let d5 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 5).card
      let d6 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 6).card
      d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  intro hprof
  rcases h.exists_distinct_compl_degree_zero_zero_one_one_forall_rest_degree_two_of_profile_three_two_two
      hcard hedge hprof with
    ⟨z₁, z₂, u, v, hz₁z₂, hz₁u, hz₁v, hz₂u, hz₂v, huv, hz₁0, hz₂0, hu1, hv1, hrest⟩
  by_cases hconn : ((Gᶜ).induce (Gᶜ.support)).Connected
  · exact
      (not_cliqueFree_of_compl_zero_zero_one_one_profile_of_connected_support
        (G := G) hcard hz₁z₂ hz₁u hz₁v hz₂u hz₂v huv hz₁0 hz₂0 hu1 hv1 hrest hconn) hfree
  · exact h.not_colorable
      (colorable_four_of_compl_zero_zero_one_one_profile_of_not_connected_support
        (G := G) hcard hz₁z₂ hz₁u hz₁v hz₂u hz₂v huv hz₁0 hz₂0 hu1 hv1 hrest hconn)

/-- The seven-vertex `|E| = 17` case is impossible for `K₅`-free incidence-critical
non-`4`-colorable graphs.

Source: the previous reduction leaves only the `(3,2,2)` profile, which is now excluded. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 17 := by
  intro hedge
  have hprof :=
    h.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge
  exact
    (h.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge) hprof

/-- On seven vertices, a `K₅`-free incidence-critical non-`4`-colorable graph has exactly `16`
edges.

Source: the previous sharp window `[16, 17]` together with the new exclusion of `|E| = 17`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card = 16 := by
  have hge : 16 ≤ G.edgeFinset.card :=
    h.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  have hle : G.edgeFinset.card ≤ 17 :=
    h.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree
  have hne : G.edgeFinset.card ≠ 17 :=
    h.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree
  omega

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift excluding the `(3,2,2)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 4).card
      let d5 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 5).card
      let d6 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 6).card
      d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

/-- Vertex-critical lift of the seven-vertex `|E| = 17` exclusion. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 17 :=
  h.toIncidenceCritical_four.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Vertex-critical lift of the exact seven-vertex edge count `|E| = 16`. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card = 16 :=
  h.toIncidenceCritical_four.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift excluding the `(3,2,2)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 4).card
      let d5 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 5).card
      let d6 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 6).card
      d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift of the seven-vertex `|E| = 17` exclusion. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 17 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift of the exact seven-vertex edge count `|E| = 16`. -/
theorem IsMinimalNonColorable.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card = 16 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift excluding the `(3,2,2)` seven-vertex `17`-edge profile under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 4).card
      let d5 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 5).card
      let d6 : ℕ := (Finset.univ.filter fun x : V => G.degree x = 6).card
      d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_profile_ne_three_two_two_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

end MinimalBridge

end FourColor.Curriculum.Actual
