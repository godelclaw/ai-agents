import FourColor.Curriculum.Actual.SevenVertexSeventeenStructure

namespace FourColor.Curriculum.Actual

section GenericFourVertex

variable {W : Type*} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- A `2`-regular graph on four vertices has a nonadjacent pair.

Source: helper theorem for the rigid `(4,0,3)` degree-count profile in the seven-vertex
`|E| = 17` branch. Each vertex has exactly two neighbors among the other three vertices, so one
other vertex is forced to be nonadjacent. -/
theorem exists_nonadjacent_pair_of_card_eq_four_of_isRegularOfDegree_two
    (hcard : Fintype.card W = 4) (hreg : H.IsRegularOfDegree 2) :
    ∃ a b : W, a ≠ b ∧ ¬ H.Adj a b := by
  classical
  have hpos : 0 < Fintype.card W := by omega
  let a : W := Classical.choice (Fintype.card_pos_iff.mp hpos)
  have hother_card :
      Fintype.card ↥((({a} : Set W)ᶜ)) = 3 := by
    calc
      Fintype.card ↥((({a} : Set W)ᶜ)) = Fintype.card W - Fintype.card ↥({a} : Set W) := by
        simpa using (Fintype.card_compl_set ({a} : Set W))
      _ = 4 - 1 := by rw [hcard]; simp
      _ = 3 := by decide
  have hother_ncard :
      (({a} : Set W)ᶜ).ncard = 3 := by
    have hother_card' : Fintype.card ↥((({a} : Set W)ᶜ)) = (({a} : Set W)ᶜ).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hother_card'] using hother_card
  have hneigh_ncard : (H.neighborSet a).ncard = 2 := by
    have hneigh_card : Fintype.card ↥(H.neighborSet a) = 2 := by
      simpa [hreg a] using (H.card_neighborSet_eq_degree (v := a))
    have hneigh_card' : Fintype.card ↥(H.neighborSet a) = (H.neighborSet a).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hneigh_card'] using hneigh_card
  have hlt : (H.neighborSet a).ncard < (({a} : Set W)ᶜ).ncard := by
    omega
  obtain ⟨b, hbmem, hbnotmem⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := H.neighborSet a) (t := ({a} : Set W)ᶜ) hlt
  have hab : a ≠ b := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hbmem
  have hnot : ¬ H.Adj a b := by
    simpa [SimpleGraph.mem_neighborSet] using hbnotmem
  exact ⟨a, b, hab, hnot⟩

end GenericFourVertex

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The `(4,0,3)` degree-count profile in the seven-vertex `|E| = 17` branch yields three
isolated complement vertices and a `2`-regular complement support on four vertices.

Source: new theorem translating the most rigid exact degree profile for the live seven-vertex
`17`-edge branch into complement structure. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_three_compl_degree_eq_zero_card_support_eq_four_and_induce_support_isRegularOfDegree_two_of_profile_four_zero_three
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) :
    ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧ Gᶜ.degree w = 0 ∧
      Fintype.card Gᶜ.support = 4 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  classical
  let s5 : Finset V := Finset.univ.filter fun v : V => G.degree v = 5
  let s6 : Finset V := Finset.univ.filter fun v : V => G.degree v = 6
  rcases hprof with ⟨_hd4, hd5, hd6⟩
  have hs5 : s5.card = 0 := by simpa [s5] using hd5
  have hs6 : s6.card = 3 := by simpa [s6] using hd6
  rcases Finset.card_eq_three.mp hs6 with ⟨u, v, w, huv, huw, hvw, hs6eq⟩
  have hu6 : G.degree u = 6 := by
    have humem : u ∈ s6 := by rw [hs6eq]; simp
    exact (Finset.mem_filter.mp humem).2
  have hv6 : G.degree v = 6 := by
    have hvmem : v ∈ s6 := by rw [hs6eq]; simp
    exact (Finset.mem_filter.mp hvmem).2
  have hw6 : G.degree w = 6 := by
    have hwmem : w ∈ s6 := by rw [hs6eq]; simp
    exact (Finset.mem_filter.mp hwmem).2
  have hu0 : Gᶜ.degree u = 0 := by
    simpa [hcard, hu6] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hv0 : Gᶜ.degree v = 0 := by
    simpa [hcard, hv6] using (SimpleGraph.degree_compl (G := G) (v := v))
  have hw0 : Gᶜ.degree w = 0 := by
    simpa [hcard, hw6] using (SimpleGraph.degree_compl (G := G) (v := w))
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hv_not_mem : v ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := v)).mp hv0
  have hw_not_mem : w ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := w)).mp hw0
  have hrest4 : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → G.degree x = 4 := by
    intro x hxu hxv hxw
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
        hcard hedge x with hx4 | hx5 | hx6
    · exact hx4
    · exfalso
      have hxmem : x ∈ s5 := by simp [s5, hx5]
      have hs5empty : s5 = ∅ := Finset.card_eq_zero.mp hs5
      simp [hs5empty] at hxmem
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6eq] at hxmem
      simp [hxu, hxv, hxw] at hxmem
  have hcomp_rest : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → Gᶜ.degree x = 2 := by
    intro x hxu hxv hxw
    simpa [hcard, hrest4 x hxu hxv hxw] using (SimpleGraph.degree_compl (G := G) (v := x))
  have hsupp :
      Gᶜ.support = ({u, v, w} : Set V)ᶜ := by
    ext x
    constructor
    · intro hx
      have hxu : x ≠ u := by
        intro hEq
        exact hu_not_mem (hEq ▸ hx)
      have hxv : x ≠ v := by
        intro hEq
        exact hv_not_mem (hEq ▸ hx)
      have hxw : x ≠ w := by
        intro hEq
        exact hw_not_mem (hEq ▸ hx)
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxu, hxv, hxw]
    · intro hx
      have hxu : x ≠ u := by
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        exact hx.1
      have hxv : x ≠ v := by
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        exact hx.2.1
      have hxw : x ≠ w := by
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        exact hx.2.2
      exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hcomp_rest x hxu hxv hxw])
  have htriple_card : Fintype.card ({u, v, w} : Set V) = 3 := by
    rw [← Set.toFinset_card]
    simp [huv, huw, hvw]
  have hcard_support : Fintype.card Gᶜ.support = 4 := by
    have hcard_support_eq :
        Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v, w} : Set V) := by
      simpa [hsupp] using (Fintype.card_compl_set ({u, v, w} : Set V))
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v, w} : Set V) := hcard_support_eq
      _ = 7 - 3 := by rw [hcard, htriple_card]
      _ = 4 := by decide
  have hreg : ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
    intro x
    rw [SimpleGraph.degree_induce_support]
    have hxsupport : (x : V) ∈ Gᶜ.support := x.property
    have hxnot : (x : V) ∈ ({u, v, w} : Set V)ᶜ := by
      simpa [hsupp] using hxsupport
    have hxu : (x : V) ≠ u := by
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hxnot
      exact hxnot.1
    have hxv : (x : V) ≠ v := by
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hxnot
      exact hxnot.2.1
    have hxw : (x : V) ≠ w := by
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hxnot
      exact hxnot.2.2
    exact hcomp_rest x hxu hxv hxw
  exact ⟨u, v, w, huv, huw, hvw, hu0, hv0, hw0, hcard_support, hreg⟩

/-- The rigid `(4,0,3)` degree-count profile in the seven-vertex `|E| = 17` branch forces a
5-clique.

Source: new theorem combining the complement profile above with the fact that a `2`-regular graph
on four vertices has a nonadjacent pair, which becomes an edge in the original graph. Together
with the three complement-isolated vertices this gives a 5-clique. -/
theorem IsIncidenceCriticalNonColorable.not_cliqueFree_of_profile_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) :
    ¬ G.CliqueFree 5 := by
  classical
  rcases h.exists_distinct_three_compl_degree_eq_zero_card_support_eq_four_and_induce_support_isRegularOfDegree_two_of_profile_four_zero_three
      hcard hedge hprof with
    ⟨u, v, w, huv, huw, hvw, hu0, hv0, hw0, hsupp, hreg⟩
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
  have habH : ∃ a b : Gᶜ.support, a ≠ b ∧ ¬ H.Adj a b := by
    simpa [H] using
      exists_nonadjacent_pair_of_card_eq_four_of_isRegularOfDegree_two (H := H) hsupp hreg
  rcases habH with ⟨a, b, hab, habnot⟩
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hv_not_mem : v ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := v)).mp hv0
  have hw_not_mem : w ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := w)).mp hw0
  have hua : u ≠ a := by
    intro hEq
    exact hu_not_mem (hEq ▸ a.property)
  have huv' : u ≠ v := huv
  have huw' : u ≠ w := huw
  have hva : v ≠ a := by
    intro hEq
    exact hv_not_mem (hEq ▸ a.property)
  have hvb : v ≠ b := by
    intro hEq
    exact hv_not_mem (hEq ▸ b.property)
  have hwa : w ≠ a := by
    intro hEq
    exact hw_not_mem (hEq ▸ a.property)
  have hwb : w ≠ b := by
    intro hEq
    exact hw_not_mem (hEq ▸ b.property)
  have hub : u ≠ b := by
    intro hEq
    exact hu_not_mem (hEq ▸ b.property)
  have habv : (a : V) ≠ (b : V) := by
    intro hEq
    apply hab
    exact Subtype.ext hEq
  have hpair : G.Adj a b := by
    by_contra habG
    exact habnot ((SimpleGraph.compl_adj G a b).2 ⟨habv, habG⟩)
  have hzero_adj_support :
      ∀ {x : V}, Gᶜ.degree x = 0 → x ≠ a → x ≠ b → G.Adj x a ∧ G.Adj x b := by
    intro x hx0 hxa hxb
    have hx_not_mem : x ∉ Gᶜ.support := by
      exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := x)).mp hx0
    have hxaG : G.Adj x a := by
      by_contra hxaG
      have hxaC : Gᶜ.Adj x a := (SimpleGraph.compl_adj G x a).2 ⟨hxa, hxaG⟩
      exact hx_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨a, hxaC⟩)
    have hxbG : G.Adj x b := by
      by_contra hxbG
      have hxbC : Gᶜ.Adj x b := (SimpleGraph.compl_adj G x b).2 ⟨hxb, hxbG⟩
      exact hx_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨b, hxbC⟩)
    exact ⟨hxaG, hxbG⟩
  have huvG : G.Adj u v := by
    by_contra huvG
    have huvC : Gᶜ.Adj u v := (SimpleGraph.compl_adj G u v).2 ⟨huv, huvG⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨v, huvC⟩)
  have huwG : G.Adj u w := by
    by_contra huwG
    have huwC : Gᶜ.Adj u w := (SimpleGraph.compl_adj G u w).2 ⟨huw, huwG⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨w, huwC⟩)
  have hvwG : G.Adj v w := by
    by_contra hvwG
    have hvwC : Gᶜ.Adj v w := (SimpleGraph.compl_adj G v w).2 ⟨hvw, hvwG⟩
    exact hv_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨w, hvwC⟩)
  have huaG : G.Adj u a := (hzero_adj_support hu0 hua hub).1
  have hubG : G.Adj u b := (hzero_adj_support hu0 hua hub).2
  have hvaG : G.Adj v a := (hzero_adj_support hv0 hva hvb).1
  have hvbG : G.Adj v b := (hzero_adj_support hv0 hva hvb).2
  have hwaG : G.Adj w a := (hzero_adj_support hw0 hwa hwb).1
  have hwbG : G.Adj w b := (hzero_adj_support hw0 hwa hwb).2
  let s : Finset V := {u, v, w, (a : V), (b : V)}
  have hsClique : G.IsClique s := by
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    simp [s] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl
    all_goals
      first
        | contradiction
        | exact huvG
        | exact huvG.symm
        | exact huwG
        | exact huwG.symm
        | exact hvwG
        | exact hvwG.symm
        | exact huaG
        | exact huaG.symm
        | exact hubG
        | exact hubG.symm
        | exact hvaG
        | exact hvaG.symm
        | exact hvbG
        | exact hvbG.symm
        | exact hwaG
        | exact hwaG.symm
        | exact hwbG
        | exact hwbG.symm
        | exact hpair
        | exact hpair.symm
  have hsCard : s.card = 5 := by
    simp [s, huv, huw, hvw, hua, hub, hva, hvb, hwa, hwb, habv]
  have hsNClique : G.IsNClique 5 s := by
    rw [SimpleGraph.isNClique_iff]
    exact ⟨hsClique, hsCard⟩
  exact hsNClique.not_cliqueFree

/-- Under `K₅`-freeness, the rigid `(4,0,3)` degree-count profile cannot occur in the
seven-vertex `|E| = 17` branch.

Source: new reduction theorem removing the most rigid exact degree profile from the live
seven-vertex `17`-edge frontier. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) := by
  intro hprof
  exact
    (h.not_cliqueFree_of_profile_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
      hcard hedge hprof) hfree

/-- Under `K₅`-freeness, the seven-vertex `|E| = 17` degree-count split drops the rigid
`(4,0,3)` branch.

Source: new theorem sharpening the exact `17`-edge case split by excluding the branch that already
forces a `K₅`. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 1 ∧ d5 = 6 ∧ d6 = 0) ∨
      (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  rcases h.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_seventeen hcard hedge with
    hcase | hcase | hcase | hcase
  · exact Or.inl hcase
  · exact Or.inr (Or.inl hcase)
  · exact Or.inr (Or.inr hcase)
  · exfalso
    exact
      (h.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
        hcard hfree hedge) hcase

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `17`-edge exclusion of the `(4,0,3)` profile. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

/-- Vertex-critical lift of the reduced seven-vertex `17`-edge degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 1 ∧ d5 = 6 ∧ d6 = 0) ∨
      (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `17`-edge exclusion of the `(4,0,3)`
profile. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `17`-edge degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 1 ∧ d5 = 6 ∧ d6 = 0) ∨
      (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift of the seven-vertex `17`-edge exclusion of the `(4,0,3)` profile
under `K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 0 ∧ d6 = 3) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_profile_ne_four_zero_three_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `17`-edge degree-count split under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 1 ∧ d5 = 6 ∧ d6 = 0) ∨
      (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

end MinimalBridge

end FourColor.Curriculum.Actual
