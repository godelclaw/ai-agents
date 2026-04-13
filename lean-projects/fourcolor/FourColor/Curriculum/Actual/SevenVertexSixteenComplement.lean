import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSixteenStructure

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The `(5,0,2)` degree-count profile in the seven-vertex `|E| = 16` branch yields two isolated
complement vertices and a `2`-regular complement support on five vertices.

Source: new theorem translating the most rigid exact degree profile in the live seven-vertex
`16`-edge frontier into complement structure. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_profile_five_zero_two
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :
    ∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
  classical
  let s5 : Finset V := Finset.univ.filter fun x : V => G.degree x = 5
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨_hd4, hd5, hd6⟩
  have hs5 : s5.card = 0 := by
    simpa [s5] using hd5
  have hs6 : s6.card = 2 := by
    simpa [s6] using hd6
  have hs5empty : s5 = ∅ := Finset.card_eq_zero.mp hs5
  rcases Finset.card_eq_two.mp hs6 with ⟨u, v, huv, hs6eq⟩
  have hu6 : G.degree u = 6 := by
    have humem : u ∈ s6 := by
      rw [hs6eq]
      simp
    exact (Finset.mem_filter.mp humem).2
  have hv6 : G.degree v = 6 := by
    have hvmem : v ∈ s6 := by
      rw [hs6eq]
      simp
    exact (Finset.mem_filter.mp hvmem).2
  have hrest4 : ∀ x : V, x ≠ u → x ≠ v → G.degree x = 4 := by
    intro x hxu hxv
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge x with hx4 | hx5 | hx6
    · exact hx4
    · have hxmem : x ∈ s5 := by simp [s5, hx5]
      rw [hs5empty] at hxmem
      simp at hxmem
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6eq] at hxmem
      simp [hxu, hxv] at hxmem
  have hu0 : Gᶜ.degree u = 0 := by
    simpa [hcard, hu6] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hv0 : Gᶜ.degree v = 0 := by
    simpa [hcard, hv6] using (SimpleGraph.degree_compl (G := G) (v := v))
  have hrest2 : ∀ x : V, x ≠ u → x ≠ v → Gᶜ.degree x = 2 := by
    intro x hxu hxv
    simpa [hcard, hrest4 x hxu hxv] using (SimpleGraph.degree_compl (G := G) (v := x))
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hv_not_mem : v ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := v)).mp hv0
  have hsupp : Gᶜ.support = ({u, v} : Set V)ᶜ := by
    ext x
    constructor
    · intro hx
      have hxu : x ≠ u := by
        intro hEq
        exact hu_not_mem (hEq ▸ hx)
      have hxv : x ≠ v := by
        intro hEq
        exact hv_not_mem (hEq ▸ hx)
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxu, hxv]
    · intro hx
      have hxu : x ≠ u := by
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        exact hx.1
      have hxv : x ≠ v := by
        simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        exact hx.2
      exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hrest2 x hxu hxv])
  have hpair_card : Fintype.card ({u, v} : Set V) = 2 := by
    rw [← Set.toFinset_card]
    simp [huv]
  have hcard_support : Fintype.card Gᶜ.support = 5 := by
    have hcard_support_eq :
        Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v} : Set V) := by
      simpa [hsupp] using (Fintype.card_compl_set ({u, v} : Set V))
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v} : Set V) := hcard_support_eq
      _ = 7 - 2 := by rw [hcard, hpair_card]
      _ = 5 := by decide
  have hreg : ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2 := by
    intro x
    rw [SimpleGraph.degree_induce_support]
    have hxnot : (x : V) ∈ ({u, v} : Set V)ᶜ := by
      simpa [hsupp] using x.property
    have hxu : (x : V) ≠ u := by
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hxnot
      exact hxnot.1
    have hxv : (x : V) ≠ v := by
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hxnot
      exact hxnot.2
    exact hrest2 x hxu hxv
  exact ⟨u, v, huv, hu0, hv0, hcard_support, hreg⟩

/-- The `(4,2,1)` degree-count profile in the seven-vertex `|E| = 16` branch yields one isolated
complement vertex, two complement degree-`1` vertices, and every other complement vertex of
degree `2`.

Source: new theorem translating the mixed exact degree profile in the live seven-vertex `16`-edge
frontier into raw complement geometry. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_compl_degree_zero_one_one_card_support_eq_six_forall_rest_degree_two_of_profile_four_two_one
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 4 ∧ d5 = 2 ∧ d6 = 1) :
    ∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
      Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
      Fintype.card Gᶜ.support = 6 ∧
      ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2 := by
  classical
  let s5 : Finset V := Finset.univ.filter fun x : V => G.degree x = 5
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨_hd4, hd5, hd6⟩
  have hs5 : s5.card = 2 := by
    simpa [s5] using hd5
  have hs6 : s6.card = 1 := by
    simpa [s6] using hd6
  rcases Finset.card_eq_one.mp hs6 with ⟨z, hs6eq⟩
  rcases Finset.card_eq_two.mp hs5 with ⟨u, v, huv, hs5eq⟩
  have hz6 : G.degree z = 6 := by
    have hzmem : z ∈ s6 := by
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
  have hrest4 : ∀ x : V, x ≠ z → x ≠ u → x ≠ v → G.degree x = 4 := by
    intro x hxz hxu hxv
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge x with hx4 | hx5 | hx6
    · exact hx4
    · have hxmem : x ∈ s5 := by simp [s5, hx5]
      rw [hs5eq] at hxmem
      simp [hxu, hxv] at hxmem
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6eq] at hxmem
      simp [hxz] at hxmem
  have hz0 : Gᶜ.degree z = 0 := by
    simpa [hcard, hz6] using (SimpleGraph.degree_compl (G := G) (v := z))
  have hu1 : Gᶜ.degree u = 1 := by
    simpa [hcard, hu5] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hv1 : Gᶜ.degree v = 1 := by
    simpa [hcard, hv5] using (SimpleGraph.degree_compl (G := G) (v := v))
  have hrest2 : ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2 := by
    intro x hxz hxu hxv
    simpa [hcard, hrest4 x hxz hxu hxv] using (SimpleGraph.degree_compl (G := G) (v := x))
  have hz_not_mem : z ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := z)).mp hz0
  have hsupp : Gᶜ.support = ({z} : Set V)ᶜ := by
    ext x
    constructor
    · intro hx
      have hxz : x ≠ z := by
        intro hEq
        exact hz_not_mem (hEq ▸ hx)
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hxz
    · intro hx
      have hxz : x ≠ z := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hx
      by_cases hxu : x = u
      · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
          subst x
          omega)
      · by_cases hxv : x = v
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            omega)
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hrest2 x hxz hxu hxv])
  have hcard_support : Fintype.card Gᶜ.support = 6 := by
    have hcard_support_eq :
        Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({z} : Set V) := by
      simpa [hsupp] using (Fintype.card_compl_set ({z} : Set V))
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({z} : Set V) := hcard_support_eq
      _ = 7 - 1 := by rw [hcard]; simp
      _ = 6 := by decide
  exact ⟨z, u, v, by
    intro hEq
    subst u
    omega, by
    intro hEq
    subst v
    omega, huv, hz0, hu1, hv1, hcard_support, hrest2⟩

/-- The `(3,4,0)` degree-count profile in the seven-vertex `|E| = 16` branch yields four
complement degree-`1` vertices and three complement degree-`2` vertices, with full complement
support.

Source: new theorem translating the endpoint-heavy exact degree profile in the live seven-vertex
`16`-edge frontier into raw complement geometry. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_four_compl_degree_eq_one_card_support_eq_seven_forall_rest_degree_two_of_profile_three_four_zero
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 3 ∧ d5 = 4 ∧ d6 = 0) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
      Fintype.card Gᶜ.support = 7 ∧
      ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2 := by
  classical
  let s5 : Finset V := Finset.univ.filter fun x : V => G.degree x = 5
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨_hd4, hd5, hd6⟩
  have hs5 : s5.card = 4 := by
    simpa [s5] using hd5
  have hs6 : s6.card = 0 := by
    simpa [s6] using hd6
  have hs6empty : s6 = ∅ := Finset.card_eq_zero.mp hs6
  rcases Finset.card_eq_four.mp hs5 with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs5eq⟩
  have ha5 : G.degree a = 5 := by
    have hamem : a ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp hamem).2
  have hb5 : G.degree b = 5 := by
    have hbmem : b ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp hbmem).2
  have hc5 : G.degree c = 5 := by
    have hcmem : c ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp hcmem).2
  have hd5' : G.degree d = 5 := by
    have hdmem : d ∈ s5 := by
      rw [hs5eq]
      simp
    exact (Finset.mem_filter.mp hdmem).2
  have hrest4 : ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → G.degree x = 4 := by
    intro x hxa hxb hxc hxd
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
        hcard hedge x with hx4 | hx5 | hx6
    · exact hx4
    · have hxmem : x ∈ s5 := by simp [s5, hx5]
      rw [hs5eq] at hxmem
      simp [hxa, hxb, hxc, hxd] at hxmem
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6empty] at hxmem
      simp at hxmem
  have ha1 : Gᶜ.degree a = 1 := by
    simpa [hcard, ha5] using (SimpleGraph.degree_compl (G := G) (v := a))
  have hb1 : Gᶜ.degree b = 1 := by
    simpa [hcard, hb5] using (SimpleGraph.degree_compl (G := G) (v := b))
  have hc1 : Gᶜ.degree c = 1 := by
    simpa [hcard, hc5] using (SimpleGraph.degree_compl (G := G) (v := c))
  have hd1 : Gᶜ.degree d = 1 := by
    simpa [hcard, hd5'] using (SimpleGraph.degree_compl (G := G) (v := d))
  have hrest2 : ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2 := by
    intro x hxa hxb hxc hxd
    simpa [hcard, hrest4 x hxa hxb hxc hxd] using (SimpleGraph.degree_compl (G := G) (v := x))
  have hsupp : Gᶜ.support = Set.univ := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      by_cases hxa : x = a
      · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
          subst x
          omega)
      · by_cases hxb : x = b
        · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
            subst x
            omega)
        · by_cases hxc : x = c
          · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
              subst x
              omega)
          · by_cases hxd : x = d
            · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by
                subst x
                omega)
            · exact (Gᶜ.degree_pos_iff_mem_support x).1 (by simp [hrest2 x hxa hxb hxc hxd])
  have hcard_support : Fintype.card Gᶜ.support = 7 := by
    simpa [hsupp, hcard]
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha1, hb1, hc1, hd1, hcard_support, hrest2⟩

/-- Complement case split for the exact seven-vertex `16`-edge branch.

Source: new theorem packaging the three exact complement-degree patterns corresponding to the three
surviving degree-count profiles in the live seven-vertex frontier. -/
theorem IsIncidenceCriticalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) := by
  rcases h.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen hcard hedge with
    hprof | hprof | hprof
  · exact Or.inr <| Or.inr <|
      h.exists_distinct_four_compl_degree_eq_one_card_support_eq_seven_forall_rest_degree_two_of_profile_three_four_zero
        hcard hedge hprof
  · exact Or.inr <| Or.inl <|
      h.exists_distinct_compl_degree_zero_one_one_card_support_eq_six_forall_rest_degree_two_of_profile_four_two_one
        hcard hedge hprof
  · exact Or.inl <|
      h.exists_distinct_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two_of_profile_five_zero_two
        hcard hedge hprof

/-- Complement case split for the live seven-vertex `K₅`-free incidence-critical branch.

Source: the exact seven-vertex frontier now has `|E| = 16`, so the raw `16`-edge complement split
becomes the current live case split. -/
theorem IsIncidenceCriticalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact h.sixteen_edge_compl_case_split_of_card_eq_seven hcard hedge

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the exact seven-vertex `16`-edge complement case split. -/
theorem IsVertexCriticalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) :=
  h.toIncidenceCritical_four.sixteen_edge_compl_case_split_of_card_eq_seven hcard hedge

/-- Vertex-critical lift of the live seven-vertex `K₅`-free complement case split. -/
theorem IsVertexCriticalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) :=
  h.toIncidenceCritical_four.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the exact seven-vertex `16`-edge complement case split. -/
theorem IsMinimalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) :=
  (h.toIncidenceCritical hadj).sixteen_edge_compl_case_split_of_card_eq_seven hcard hedge

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free complement case split. -/
theorem IsMinimalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) :=
  (h.toIncidenceCritical hadj).sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free complement case split without a
separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    (∃ u v : V, u ≠ v ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      Fintype.card Gᶜ.support = 5 ∧
      ((Gᶜ).induce (Gᶜ.support)).IsRegularOfDegree 2) ∨
      (∃ z u v : V, z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
        Gᶜ.degree z = 0 ∧ Gᶜ.degree u = 1 ∧ Gᶜ.degree v = 1 ∧
        Fintype.card Gᶜ.support = 6 ∧
        ∀ x : V, x ≠ z → x ≠ u → x ≠ v → Gᶜ.degree x = 2) ∨
      (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        Gᶜ.degree a = 1 ∧ Gᶜ.degree b = 1 ∧ Gᶜ.degree c = 1 ∧ Gᶜ.degree d = 1 ∧
        Fintype.card Gᶜ.support = 7 ∧
        ∀ x : V, x ≠ a → x ≠ b → x ≠ c → x ≠ d → Gᶜ.degree x = 2) := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.sixteen_edge_compl_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
