import Mathlib.Combinatorics.SimpleGraph.Acyclic
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointPaths
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointCases
import FourColor.Curriculum.Actual.SevenVertexMinimalEdgeBounds
import FourColor.Curriculum.Actual.SevenVertexRealization
import FourColor.Curriculum.Actual.SevenVertexSixteenComplement

namespace FourColor.Curriculum.Actual

section Generic

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- In a connected component of a finite graph whose vertices all have degree `1` or `2`, any
degree-`1` vertex has a unique degree-`1` partner in that component, and all other component
vertices have degree `2`.

Source: helper theorem for the seven-vertex `|E| = 16` profile `(3,4,0)`, isolating path
components inside a graph with four endpoints and three degree-`2` vertices. -/
theorem exists_partner_and_forall_degree_eq_two_on_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
    (c : H.ConnectedComponent) {u : W} (hu : u ∈ c.supp) (hu1 : H.degree u = 1)
    (hdeg : ∀ w : W, w ∈ c.supp → H.degree w = 1 ∨ H.degree w = 2) :
    ∃ v : W, v ∈ c.supp ∧ v ≠ u ∧ H.degree v = 1 ∧
      ∀ w : W, w ∈ c.supp → w ≠ u → w ≠ v → H.degree w = 2 := by
  classical
  let K : SimpleGraph c.supp := H.induce c.supp
  let uS : c.supp := ⟨u, hu⟩
  have hKconn : K.Connected := by
    simpa [K, SimpleGraph.ConnectedComponent.toSimpleGraph] using c.connected_toSimpleGraph
  have hdeg_eq : ∀ x : c.supp, K.degree x = H.degree x := by
    intro x
    simpa [K] using
      (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
        (v := x)
        (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) x.property))
  have huK1 : K.degree uS = 1 := by
    simpa [uS] using (hdeg_eq uS).trans hu1
  let s1 : Finset c.supp := Finset.univ.filter fun x : c.supp => K.degree x = 1
  have huS_mem : uS ∈ s1 := by
    simp [s1, huK1]
  have hs1_pos : 0 < s1.card := Finset.card_pos.mpr ⟨uS, huS_mem⟩
  have hdegK : ∀ x : c.supp, K.degree x = 1 ∨ K.degree x = 2 := by
    intro x
    simpa [hdeg_eq x] using hdeg x x.property
  let sNot : Finset c.supp := Finset.univ.filter fun x : c.supp => K.degree x ≠ 1
  have hsum_split :
      ∑ x : c.supp, K.degree x =
        Finset.sum s1 (fun x => K.degree x) +
          Finset.sum sNot (fun x => K.degree x) := by
    simpa [s1, sNot] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun x : c.supp => K.degree x = 1) (f := fun x : c.supp => K.degree x)).symm
  have hsum_s1 : Finset.sum s1 (fun x => K.degree x) = s1.card := by
    calc
      Finset.sum s1 (fun x => K.degree x) = Finset.sum s1 (fun _ => 1) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hx1 : K.degree x = 1 := by
          simp [s1] at hx
          exact hx
        exact hx1
      _ = s1.card := by simp
  have hsum_not :
      Finset.sum sNot (fun x => K.degree x) = 2 * sNot.card := by
    calc
      Finset.sum sNot (fun x => K.degree x) = Finset.sum sNot (fun _ => 2) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxne : K.degree x ≠ 1 := by
          simp [sNot] at hx
          exact hx
        rcases hdegK x with hx1 | hx2
        · exact False.elim (hxne hx1)
        · exact hx2
      _ = 2 * sNot.card := by
        simpa [two_mul, Nat.mul_comm]
  have hs1_card_split :
      s1.card + sNot.card = Fintype.card c.supp := by
    simpa [s1, Finset.card_univ] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
        (p := fun x : c.supp => K.degree x = 1))
  have hcard_edge :
      Fintype.card c.supp ≤ K.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hKconn.card_vert_le_card_edgeSet_add_one
  have hs1_le_two : s1.card ≤ 2 := by
    have hsum_edges : ∑ x : c.supp, K.degree x = 2 * K.edgeFinset.card := by
      simpa using K.sum_degrees_eq_twice_card_edges
    have hsum_ge :
        2 * Fintype.card c.supp - 2 ≤ ∑ x : c.supp, K.degree x := by
      omega
    have hsum_eq :
        ∑ x : c.supp, K.degree x = s1.card + 2 * sNot.card := by
      rw [hsum_split, hsum_s1, hsum_not]
    omega
  have hfilter_eq :
      (Finset.univ.filter fun x : c.supp => Odd (K.degree x)) = s1 := by
    ext x
    rcases hdegK x with hx1 | hx2
    · simp [s1, hx1]
    · simp [s1, hx2]
  have hs1_even : Even s1.card := by
    have hsum_even : Even (∑ x : c.supp, K.degree x) := by
      refine ⟨K.edgeFinset.card, ?_⟩
      simpa [two_mul] using K.sum_degrees_eq_twice_card_edges
    by_cases hs1odd : Odd s1.card
    · have hsum_odd : Odd (∑ x : c.supp, K.degree x) := by
        rw [Finset.odd_sum_iff_odd_card_odd]
        simpa [hfilter_eq] using hs1odd
      exact False.elim ((Nat.not_even_iff_odd.mpr hsum_odd) hsum_even)
    · exact Nat.not_odd_iff_even.mp hs1odd
  have hs1_two : s1.card = 2 := by
    rcases hs1_even with ⟨m, hm⟩
    omega
  rcases Finset.card_eq_two.mp hs1_two with ⟨x, y, hxy, hs1eq⟩
  have hu_cases : uS = x ∨ uS = y := by
    have hu_mem' : uS ∈ ({x, y} : Finset c.supp) := by
      rw [← hs1eq]
      exact huS_mem
    simpa using hu_mem'
  rcases hu_cases with hux | huy
  · let vS : c.supp := y
    have hs1uv : s1 = ({uS, vS} : Finset c.supp) := by
      simpa [vS, hux] using hs1eq
    have hvS_mem : (vS : W) ∈ c.supp := vS.property
    have hvS_ne : vS ≠ uS := by
      simpa [vS, hux] using hxy.symm
    have hv1 : H.degree (vS : W) = 1 := by
      have hvS_mem_filter : vS ∈ s1 := by
        rw [hs1uv]
        simp
      exact (hdeg_eq vS).symm.trans ((Finset.mem_filter.mp hvS_mem_filter).2)
    refine ⟨vS, hvS_mem, ?_, hv1, ?_⟩
    · intro hEq
      exact hvS_ne (Subtype.ext hEq)
    · intro w hw hwu hwv
      rcases hdeg w hw with hw1 | hw2
      · have hwS_mem : (⟨w, hw⟩ : c.supp) ∈ s1 := by
          simp [s1, hdeg_eq ⟨w, hw⟩, hw1]
        have hwuS : (⟨w, hw⟩ : c.supp) ≠ uS := by
          intro hEq
          exact hwu (Subtype.ext_iff.mp hEq)
        have hwvS : (⟨w, hw⟩ : c.supp) ≠ vS := by
          intro hEq
          exact hwv (Subtype.ext_iff.mp hEq)
        rw [hs1uv] at hwS_mem
        simp [hwuS, hwvS] at hwS_mem
      · exact hw2
  · let vS : c.supp := x
    have hs1uv : s1 = ({uS, vS} : Finset c.supp) := by
      simpa [vS, huy, Finset.pair_comm] using hs1eq
    have hvS_mem : (vS : W) ∈ c.supp := vS.property
    have hvS_ne : vS ≠ uS := by
      simpa [vS, huy] using hxy
    have hv1 : H.degree (vS : W) = 1 := by
      have hvS_mem_filter : vS ∈ s1 := by
        rw [hs1uv]
        simp
      exact (hdeg_eq vS).symm.trans ((Finset.mem_filter.mp hvS_mem_filter).2)
    refine ⟨vS, hvS_mem, ?_, hv1, ?_⟩
    · intro hEq
      exact hvS_ne (Subtype.ext hEq)
    · intro w hw hwu hwv
      rcases hdeg w hw with hw1 | hw2
      · have hwS_mem : (⟨w, hw⟩ : c.supp) ∈ s1 := by
          simp [s1, hdeg_eq ⟨w, hw⟩, hw1]
        have hwuS : (⟨w, hw⟩ : c.supp) ≠ uS := by
          intro hEq
          exact hwu (Subtype.ext_iff.mp hEq)
        have hwvS : (⟨w, hw⟩ : c.supp) ≠ vS := by
          intro hEq
          exact hwv (Subtype.ext_iff.mp hEq)
        rw [hs1uv] at hwS_mem
        simp [hwuS, hwvS] at hwS_mem
      · exact hw2

/-- A connected component in which one vertex has degree `1` and every component vertex has degree
`1` or `2` is realized by a path covering that component support.

Source: helper theorem for the seven-vertex `|E| = 16` profile `(3,4,0)`, packaging the previous
endpoint-partner extraction with the connected path realization theorem. -/
theorem exists_partner_and_path_covering_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
    (c : H.ConnectedComponent) {u : W} (hu : u ∈ c.supp) (hu1 : H.degree u = 1)
    (hdeg : ∀ w : W, w ∈ c.supp → H.degree w = 1 ∨ H.degree w = 2) :
    ∃ v : W, v ∈ c.supp ∧ v ≠ u ∧ H.degree v = 1 ∧
      (∀ w : W, w ∈ c.supp → w ≠ u → w ≠ v → H.degree w = 2) ∧
      ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.verts = c.supp := by
  classical
  rcases
      exists_partner_and_forall_degree_eq_two_on_connectedComponent_of_mem_degree_eq_one_and_forall_mem_degree_eq_one_or_two
        (H := H) c hu hu1 hdeg with
    ⟨v, hv, hvu, hv1, hrest⟩
  let K : SimpleGraph c.supp := H.induce c.supp
  let uS : c.supp := ⟨u, hu⟩
  let vS : c.supp := ⟨v, hv⟩
  have hKconn : K.Connected := by
    simpa [K, SimpleGraph.ConnectedComponent.toSimpleGraph] using c.connected_toSimpleGraph
  have huK1 : K.degree uS = 1 := by
    simpa [K, uS] using
      (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
        (v := uS)
        (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) hu)).trans hu1
  have hvK1 : K.degree vS = 1 := by
    simpa [K, vS] using
      (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
        (v := vS)
        (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) hv)).trans hv1
  have hrestK : ∀ w : c.supp, w ≠ uS → w ≠ vS → K.degree w = 2 := by
    intro w hwu hwv
    have hdeg_eq : K.degree w = H.degree w := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
          (v := w)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) w.property))
    exact hdeg_eq.trans
      (hrest w w.property
        (fun h => hwu (Subtype.ext h))
        (fun h => hwv (Subtype.ext h)))
  rcases
      exists_path_covering_all_vertices_of_connected_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := K) hKconn
        (by
          intro hEq
          exact hvu (Subtype.ext_iff.mp hEq).symm)
        huK1 hvK1 hrestK with
    ⟨p, hp, hpverts⟩
  let φ : K →g H :=
    { toFun := fun x => x.1
      map_rel' := by
        intro a b hab
        exact hab }
  refine ⟨v, hv, hvu, hv1, hrest, p.map φ, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp
  · ext w
    constructor
    · intro hw'
      rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map] at hw'
      rcases List.mem_map.mp hw' with ⟨x, hx, rfl⟩
      exact x.property
    · intro hw'
      rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map]
      refine List.mem_map.mpr ?_
      refine ⟨⟨w, hw'⟩, ?_, rfl⟩
      rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpverts]
      simp

/-- Any connected component all of whose vertices have degree `2` is realized by a cycle covering
that component support.

Source: helper theorem for the seven-vertex `|E| = 16` profile `(3,4,0)`, used to extract the
remaining `C₃` component in the `P₂ ⊔ P₂ ⊔ C₃` branch. -/
theorem exists_cycle_covering_connectedComponent_of_forall_degree_eq_two
    (c : H.ConnectedComponent) (hdeg : ∀ w : W, w ∈ c.supp → H.degree w = 2) :
    ∃ x : W, ∃ q : H.Walk x x, q.IsCycle ∧ q.toSubgraph.verts = c.supp := by
  classical
  let K : SimpleGraph c.supp := H.induce c.supp
  have hKconn : K.Connected := by
    simpa [K, SimpleGraph.ConnectedComponent.toSimpleGraph] using c.connected_toSimpleGraph
  have hKreg : K.IsRegularOfDegree 2 := by
    intro x
    have hdeg_eq : K.degree x = H.degree x := by
      simpa [K] using
        (SimpleGraph.degree_induce_of_neighborSet_subset (G := H) (s := c.supp)
          (v := x)
          (SimpleGraph.ConnectedComponent.neighborSet_subset_supp (H := H) (c := c) x.property))
    exact hdeg_eq.trans (hdeg x x.property)
  rcases exists_cycle_covering_all_vertices_of_connected_of_isRegularOfDegree_two
      (G := K) hKconn hKreg with
    ⟨x, p, hp, hpverts⟩
  let φ : K →g H :=
    { toFun := fun y => y.1
      map_rel' := by
        intro a b hab
        exact hab }
  refine ⟨x, p.map φ, hp.map Subtype.val_injective, ?_⟩
  ext w
  constructor
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map] at hw
    rcases List.mem_map.mp hw with ⟨y, hy, rfl⟩
    exact y.property
  · intro hw
    rw [SimpleGraph.Walk.mem_verts_toSubgraph, SimpleGraph.Walk.support_map]
    refine List.mem_map.mpr ?_
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hpverts]
    simp

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The seven-vertex `|E| = 16` degree-count profile `(3,4,0)` already forces two distinct
complement path components.

Source: new structural theorem for the remaining exact seven-vertex `16`-edge branch, extracting
two explicit path components from the raw four-endpoint complement geometry. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_path_components_of_profile_three_four_zero
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    ∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp := by
  classical
  let H : SimpleGraph V := Gᶜ
  rcases
      h.exists_distinct_four_compl_degree_eq_one_card_support_eq_seven_forall_rest_degree_two_of_profile_three_four_zero
        hcard hedge hprof with
    ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha1, hb1, hc1, hd1, hsupp, hrest⟩
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
  have hsupp_eq : H.support = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hdeg12 x with hx1 | hx2
      · exact (H.degree_pos_iff_mem_support x).1 (by simp [hx1])
      · exact (H.degree_pos_iff_mem_support x).1 (by simp [hx2])
  let c₁ : H.ConnectedComponent := H.connectedComponentMk a
  have ha_c₁ : a ∈ c₁.supp := by
    simpa [c₁] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := a))
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
    let c₂ : H.ConnectedComponent := H.connectedComponentMk c
    have hc_c₂ : c ∈ c₂.supp := by
      simpa [c₂] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := c))
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
    exact ⟨c₁, c₂, hc₂_ne_c₁.symm, a, b, hab, p₁, hp₁, hp₁verts, c, v₂, hv₂c.symm, p₂, hp₂, hp₂verts⟩
  · subst v₁
    have hc_c₁ : c ∈ c₁.supp := by simpa using hv₁_c₁
    have hb_not_c₁ : b ∉ c₁.supp := by
      intro hb_c₁
      have hb2 : H.degree b = 2 := hrest_c₁ b hb_c₁ hab.symm hbc
      exact (show (1 : ℕ) ≠ 2 by decide) (hb1.symm.trans hb2)
    let c₂ : H.ConnectedComponent := H.connectedComponentMk b
    have hb_c₂ : b ∈ c₂.supp := by
      simpa [c₂] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := b))
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
    exact ⟨c₁, c₂, hc₂_ne_c₁.symm, a, c, hac, p₁, hp₁, hp₁verts, b, v₂, hv₂b.symm, p₂, hp₂, hp₂verts⟩
  · subst v₁
    have hd_c₁ : d ∈ c₁.supp := by simpa using hv₁_c₁
    have hb_not_c₁ : b ∉ c₁.supp := by
      intro hb_c₁
      have hb2 : H.degree b = 2 := hrest_c₁ b hb_c₁ hab.symm hbd
      exact (show (1 : ℕ) ≠ 2 by decide) (hb1.symm.trans hb2)
    let c₂ : H.ConnectedComponent := H.connectedComponentMk b
    have hb_c₂ : b ∈ c₂.supp := by
      simpa [c₂] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := H) (v := b))
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
    exact ⟨c₁, c₂, hc₂_ne_c₁.symm, a, d, had, p₁, hp₁, hp₁verts, b, v₂, hv₂b.symm, p₂, hp₂, hp₂verts⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `16`-edge `(3,4,0)` two-path split. -/
theorem IsVertexCriticalNonColorable.exists_distinct_path_components_of_profile_three_four_zero
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    ∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp := by
  exact
    IsIncidenceCriticalNonColorable.exists_distinct_path_components_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical_four) hcard hedge hprof

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `16`-edge `(3,4,0)` two-path split. -/
theorem IsMinimalNonColorable.exists_distinct_path_components_of_profile_three_four_zero_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    ∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
        ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp := by
  exact
    IsIncidenceCriticalNonColorable.exists_distinct_path_components_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free `(3,4,0)` two-path split
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_distinct_path_components_of_profile_three_four_zero_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    ∃ c d : (Gᶜ).ConnectedComponent, c ≠ d ∧
      ∃ u₁ v₁ : V, u₁ ≠ v₁ ∧
      ∃ p : (Gᶜ).Walk u₁ v₁, p.IsPath ∧ p.toSubgraph.verts = c.supp ∧
      ∃ u₂ v₂ : V, u₂ ≠ v₂ ∧
        ∃ q : (Gᶜ).Walk u₂ v₂, q.IsPath ∧ q.toSubgraph.verts = d.supp := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.exists_distinct_path_components_of_profile_three_four_zero
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge hprof

end MinimalBridge

end FourColor.Curriculum.Actual
