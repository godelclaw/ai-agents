import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import FourColor.Curriculum.Actual.SevenVertexFifteenComplement

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- Every neighbor of a vertex in a connected component stays inside that component. -/
theorem SimpleGraph.ConnectedComponent.neighborSet_subset_supp
    {c : H.ConnectedComponent} {u : W} (hu : u ∈ c.supp) :
    H.neighborSet u ⊆ c.supp := by
  intro w huw
  exact c.mem_supp_of_adj_mem_supp hu huw

/-- In a finite graph with exactly two degree-`1` vertices and every other vertex of degree `2`,
those two degree-`1` vertices lie in the same connected component.

Source: new helper theorem for the remaining seven-vertex `15`-edge complement branch. The proof
applies the handshaking lemma inside the connected component of one endpoint. -/
theorem reachable_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    H.Reachable u v := by
  classical
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have hu_mem : u ∈ c.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := u)
  by_cases hv_mem : v ∈ c.supp
  · exact c.reachable_of_mem_supp hu_mem hv_mem
  · let K : SimpleGraph c.supp := H.induce c.supp
    have hu_deg_comp : K.degree ⟨u, hu_mem⟩ = 1 := by
      have hdeg_eq : K.degree ⟨u, hu_mem⟩ = H.degree u := by
        simpa [K] using
          (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
            (v := ⟨u, hu_mem⟩)
            (SimpleGraph.ConnectedComponent.neighborSet_subset_supp
              (H := H) (c := c) hu_mem))
      exact hdeg_eq.trans hu1
    have hfilter_eq :
        (Finset.univ.filter fun x : c.supp => Odd (K.degree x)) = {⟨u, hu_mem⟩} := by
      ext x
      constructor
      · intro hx
        have hxodd : Odd (K.degree x) := by
          simpa using (Finset.mem_filter.mp hx).2
        have hx_ne_v : (x : W) ≠ v := by
          intro hxv
          exact hv_mem (hxv ▸ x.property)
        by_cases hxu : (x : W) = u
        · exact by
            apply Finset.mem_singleton.mpr
            exact Subtype.ext hxu
        · have hx_deg_comp : K.degree x = 2 := by
            have hdeg_eq : K.degree x = H.degree x := by
              simpa [K] using
                (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
                  (v := x)
                  (SimpleGraph.ConnectedComponent.neighborSet_subset_supp
                    (H := H) (c := c) x.property))
            exact hdeg_eq.trans (hrest x hxu hx_ne_v)
          have hx_not_odd : ¬ Odd (K.degree x) := by
            simpa [hx_deg_comp]
          exact False.elim (hx_not_odd hxodd)
      · intro hx
        rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        have hxu : x = ⟨u, hu_mem⟩ := by simpa using hx
        subst x
        simpa [hu_deg_comp]
    have hodd_sum : Odd (∑ x : c.supp, K.degree x) := by
      rw [Finset.odd_sum_iff_odd_card_odd]
      simpa [hfilter_eq]
    have hsum_even : Even (∑ x : c.supp, K.degree x) := by
      refine ⟨K.edgeFinset.card, ?_⟩
      simpa [two_mul] using K.sum_degrees_eq_twice_card_edges
    have hnot_even : ¬ Even (∑ x : c.supp, K.degree x) := by
      rwa [Nat.not_even_iff_odd]
    exact False.elim (hnot_even hsum_even)

/-- A connected finite graph with exactly two degree-`1` vertices and every other vertex of
degree `2` is a single path covering all vertices.

Source: new helper theorem turning the remaining seven-vertex `15`-edge complement branch into a
path component. The proof shows that any vertex outside a path between the endpoints would force an
extra neighbor at some vertex on the path. -/
theorem exists_path_covering_all_vertices_of_connected_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
    (hconn : H.Connected) {u v : W} (huv : u ≠ v) (hu1 : H.degree u = 1) (hv1 : H.degree v = 1)
    (hrest : ∀ w : W, w ≠ u → w ≠ v → H.degree w = 2) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = Set.univ := by
  classical
  obtain ⟨p, hp⟩ := hconn.exists_isPath u v
  have hp_not_nil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    by_contra hlen
    exact huv (p.eq_of_length_eq_zero (by omega))
  refine ⟨p, hp, Set.eq_univ_of_forall ?_⟩
  intro w
  by_contra hw_verts
  have hw_support : w ∉ p.support := by
    intro hw
    exact hw_verts (p.mem_verts_toSubgraph.mpr hw)
  obtain ⟨q, hq⟩ := hconn.exists_isPath w u
  let s : Finset W := p.support.toFinset
  have hs_nonempty : {x ∈ s | x ∈ q.support}.Nonempty := by
    refine ⟨u, by simp [s, p.start_mem_support, q.end_mem_support]⟩
  obtain ⟨x, hx_s, hx_q, hx_first⟩ := q.exists_mem_support_forall_mem_support_imp_eq s hs_nonempty
  have hx_p : x ∈ p.support := by
    simpa [s] using hx_s
  let qx : H.Walk w x := q.takeUntil x hx_q
  have hqx_not_nil : ¬ qx.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    by_contra hlen
    have hwx : w ≠ x := by
      intro hwx
      exact hw_support (hwx ▸ hx_p)
    exact hwx (qx.eq_of_length_eq_zero (by omega))
  let y : W := qx.penultimate
  have hy_adj : H.Adj y x := qx.adj_penultimate hqx_not_nil
  have hy_qx : y ∈ qx.support := by
    exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      ⟨qx.length - 1, rfl, Nat.sub_le _ _⟩
  have hy_not_p : y ∉ p.support := by
    intro hy_p
    have hy_eq_x : y = x := hx_first y (by simpa [s] using hy_p) hy_qx
    exact H.loopless x (hy_eq_x ▸ hy_adj)
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx_p with ⟨i, hxi, hi_le⟩
  by_cases hi0 : i = 0
  · have hxu : x = u := by
      calc
        x = p.getVert i := hxi.symm
        _ = u := (hp.getVert_eq_start_iff hi_le).2 hi0
    have hsnd_adj : H.Adj u p.snd := p.adj_snd hp_not_nil
    have hsnd_support : p.snd ∈ p.support := by
      exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
        ⟨1, by simp [SimpleGraph.Walk.snd], by
          have hlen : 0 < p.length := (SimpleGraph.Walk.not_nil_iff_lt_length.mp hp_not_nil)
          omega⟩
    have hy_adj_u : H.Adj u y := by
      simpa [hxu] using hy_adj.symm
    have hsnd_ne_y : p.snd ≠ y := by
      intro hy_eq
      exact hy_not_p (hy_eq.symm ▸ hsnd_support)
    let t : Finset W := {p.snd, y}
    have ht_subset : t ⊆ H.neighborFinset u := by
      intro a ha
      simp [t] at ha
      rcases ha with rfl | rfl
      · simpa using hsnd_adj
      · simpa using hy_adj_u
    have ht_card : t.card = 2 := by
      simp [t, hsnd_ne_y]
    have hu_deg_ge : 2 ≤ H.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        2 = t.card := by simpa [ht_card]
        _ ≤ (H.neighborFinset u).card := Finset.card_le_card ht_subset
    omega
  · by_cases hiend : i = p.length
    · have hxv : x = v := by
        calc
          x = p.getVert i := hxi.symm
          _ = v := (hp.getVert_eq_end_iff hi_le).2 hiend
      have hpen_adj : H.Adj v p.penultimate := (p.adj_penultimate hp_not_nil).symm
      have hpen_support : p.penultimate ∈ p.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨p.length - 1, rfl, Nat.sub_le _ _⟩
      have hy_adj_v : H.Adj v y := by
        simpa [hxv] using hy_adj.symm
      have hpen_ne_y : p.penultimate ≠ y := by
        intro hy_eq
        exact hy_not_p (hy_eq.symm ▸ hpen_support)
      let t : Finset W := {p.penultimate, y}
      have ht_subset : t ⊆ H.neighborFinset v := by
        intro a ha
        simp [t] at ha
        rcases ha with rfl | rfl
        · simpa using hpen_adj
        · simpa using hy_adj_v
      have ht_card : t.card = 2 := by
        simp [t, hpen_ne_y]
      have hv_deg_ge : 2 ≤ H.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          2 = t.card := by simpa [ht_card]
          _ ≤ (H.neighborFinset v).card := Finset.card_le_card ht_subset
      omega
    · have hi_lt : i < p.length := by omega
      have hx_ne_u : x ≠ u := by
        intro hxu
        have : i = 0 := (hp.getVert_eq_start_iff hi_le).1 (by simpa [hxi, hxu])
        exact hi0 this
      have hx_ne_v : x ≠ v := by
        intro hxv
        have : i = p.length := (hp.getVert_eq_end_iff hi_le).1 (by simpa [hxi, hxv])
        exact hiend this
      let z₁ : W := p.getVert (i - 1)
      let z₂ : W := p.getVert (i + 1)
      have hz₁_adj : H.Adj x z₁ := by
        have hi_prev : i - 1 < p.length := by omega
        have : H.Adj (p.getVert (i - 1)) (p.getVert ((i - 1) + 1)) :=
          p.adj_getVert_succ hi_prev
        have hsub : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)
        simpa [z₁, hxi, hsub] using this.symm
      have hz₂_adj : H.Adj x z₂ := by
        have : H.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hi_lt
        simpa [z₂, hxi] using this
      have hz₁_support : z₁ ∈ p.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨i - 1, by simp [z₁], by omega⟩
      have hz₂_support : z₂ ∈ p.support := by
        exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨i + 1, by simp [z₂], by omega⟩
      have hy_ne_z₁ : y ≠ z₁ := by
        intro hyz
        exact hy_not_p (hyz ▸ hz₁_support)
      have hy_ne_z₂ : y ≠ z₂ := by
        intro hyz
        exact hy_not_p (hyz ▸ hz₂_support)
      have hz₁_ne_z₂ : z₁ ≠ z₂ := by
        intro hz
        have hidx : i - 1 = i + 1 := hp.getVert_injOn
          (by rw [Set.mem_setOf_eq]; omega)
          (by rw [Set.mem_setOf_eq]; omega)
          (by simpa [z₁, z₂] using hz)
        omega
      let t : Finset W := {y, z₁, z₂}
      have ht_subset : t ⊆ H.neighborFinset x := by
        intro a ha
        simp [t] at ha
        rcases ha with rfl | rfl | rfl
        · simpa using hy_adj.symm
        · simpa using hz₁_adj
        · simpa using hz₂_adj
      have ht_card : t.card = 3 := by
        simp [t, hy_ne_z₁, hy_ne_z₂, hz₁_ne_z₂]
      have hx_deg_ge : 3 ≤ H.degree x := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        calc
          3 = t.card := by simpa [ht_card]
          _ ≤ (H.neighborFinset x).card := Finset.card_le_card ht_subset
      have hx_deg_two : H.degree x = 2 := hrest x hx_ne_u hx_ne_v
      omega

end Generic

end FourColor.Curriculum.Actual
