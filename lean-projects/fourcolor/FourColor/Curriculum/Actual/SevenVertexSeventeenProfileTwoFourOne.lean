import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexSeventeenProfileOneSixZero

namespace FourColor.Curriculum.Actual

section DegreeHelpers

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

/-- A degree-`1` vertex has a unique neighbor.

Source: helper theorem for the remaining seven-vertex `|E| = 17` profile `(2,4,1)`. -/
theorem SimpleGraph.existsUnique_adj_of_degree_eq_one
    {v : V} (hv : G.degree v = 1) :
    ∃! w : V, G.Adj v w := by
  let M : SimpleGraph.Subgraph G := ⊤
  letI : DecidableRel M.Adj := by
    intro a b
    change Decidable (G.Adj a b)
    infer_instance
  letI : ∀ x : V, Fintype ↑(M.neighborSet x) := fun x =>
    SimpleGraph.Subgraph.finiteAt (G := G) (G' := M) ⟨x, by simp [M]⟩
  letI : ∀ x : V, Fintype ↑(M.spanningCoe.neighborSet x) := fun x =>
    by simpa [M, SimpleGraph.Subgraph.spanningCoe_top] using
      (inferInstance : Fintype ↑(G.neighborSet x))
  have hvM : M.degree v = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe (G' := M) (v := v)]
    simpa [M, SimpleGraph.Subgraph.spanningCoe_top] using hv
  exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj (G' := M) (v := v)).mp hvM

/-- If a degree-`2` vertex has one known neighbor, then it has exactly one other neighbor.

Source: helper theorem for splitting the remaining seven-vertex `|E| = 17` profile `(2,4,1)` by
whether the two complement degree-`2` vertices are adjacent. -/
theorem SimpleGraph.exists_other_neighbor_of_degree_eq_two
    {v w : V} (hv : G.degree v = 2) (hvw : G.Adj v w) :
    ∃ x : V, x ≠ w ∧ G.Adj v x ∧ ∀ y : V, G.Adj v y → y = w ∨ y = x := by
  classical
  have hneigh_card : Fintype.card ↥(G.neighborSet v) = 2 := by
    simpa [hv] using (G.card_neighborSet_eq_degree (v := v))
  have hneigh_ncard : (G.neighborSet v).ncard = 2 := by
    have hcard_eq : Fintype.card ↥(G.neighborSet v) = (G.neighborSet v).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hneigh_card
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp hneigh_ncard
  have hwmem : w ∈ G.neighborSet v := by
    simpa [SimpleGraph.mem_neighborSet] using hvw
  rw [hset] at hwmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
  rcases hwmem with rfl | rfl
  · refine ⟨b, hab.symm, ?_, ?_⟩
    · have : b ∈ G.neighborSet v := by rw [hset]; simp
      simpa [SimpleGraph.mem_neighborSet] using this
    · intro y hvy
      have hymem : y ∈ G.neighborSet v := by
        simpa [SimpleGraph.mem_neighborSet] using hvy
      rw [hset] at hymem
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hymem
  · refine ⟨a, hab, ?_, ?_⟩
    · have : a ∈ G.neighborSet v := by rw [hset]; simp
      simpa [SimpleGraph.mem_neighborSet] using this
    · intro y hvy
      have hymem : y ∈ G.neighborSet v := by
        simpa [SimpleGraph.mem_neighborSet] using hvy
      rw [hset] at hymem
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm, or_comm] using hymem

end DegreeHelpers

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The `(2,4,1)` degree-count profile in the seven-vertex `|E| = 17` branch gives one isolated
complement vertex, two complement degree-`2` vertices, and four complement degree-`1` vertices.

Source: new theorem translating the next exact seven-vertex `17`-edge degree profile into raw
complement geometry before the final adjacency split. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_compl_degree_zero_two_two_forall_rest_degree_one_of_profile_two_four_one
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 2 ∧ d5 = 4 ∧ d6 = 1) :
    ∃ u p q : V, u ≠ p ∧ u ≠ q ∧ p ≠ q ∧
      Gᶜ.degree u = 0 ∧ Gᶜ.degree p = 2 ∧ Gᶜ.degree q = 2 ∧
      ∀ x : V, x ≠ u → x ≠ p → x ≠ q → Gᶜ.degree x = 1 := by
  classical
  let s4 : Finset V := Finset.univ.filter fun x : V => G.degree x = 4
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨hd4, _hd5, hd6⟩
  have hs4 : s4.card = 2 := by
    simpa [s4] using hd4
  have hs6 : s6.card = 1 := by
    simpa [s6] using hd6
  rcases Finset.card_eq_one.mp hs6 with ⟨u, hs6eq⟩
  rcases Finset.card_eq_two.mp hs4 with ⟨p, q, hpq, hs4eq⟩
  have hu6 : G.degree u = 6 := by
    have humem : u ∈ s6 := by
      rw [hs6eq]
      simp
    exact (Finset.mem_filter.mp humem).2
  have hp4 : G.degree p = 4 := by
    have hpmem : p ∈ s4 := by
      rw [hs4eq]
      simp
    exact (Finset.mem_filter.mp hpmem).2
  have hq4 : G.degree q = 4 := by
    have hqmem : q ∈ s4 := by
      rw [hs4eq]
      simp
    exact (Finset.mem_filter.mp hqmem).2
  have hrest5 : ∀ x : V, x ≠ u → x ≠ p → x ≠ q → G.degree x = 5 := by
    intro x hxu hxp hxq
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
        hcard hedge x with hx4 | hx5 | hx6
    · have hxmem : x ∈ s4 := by simp [s4, hx4]
      rw [hs4eq] at hxmem
      simp [hxp, hxq] at hxmem
    · exact hx5
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6eq] at hxmem
      simp [hxu] at hxmem
  have hu0 : Gᶜ.degree u = 0 := by
    simpa [hcard, hu6] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hp2 : Gᶜ.degree p = 2 := by
    simpa [hcard, hp4] using (SimpleGraph.degree_compl (G := G) (v := p))
  have hq2 : Gᶜ.degree q = 2 := by
    simpa [hcard, hq4] using (SimpleGraph.degree_compl (G := G) (v := q))
  have hrest1 : ∀ x : V, x ≠ u → x ≠ p → x ≠ q → Gᶜ.degree x = 1 := by
    intro x hxu hxp hxq
    simpa [hcard, hrest5 x hxu hxp hxq] using (SimpleGraph.degree_compl (G := G) (v := x))
  exact ⟨u, p, q, by
    intro hEq
    subst p
    omega, by
    intro hEq
    subst q
    omega, hpq, hu0, hp2, hq2, hrest1⟩

/-- If the remaining complement profile has one isolated vertex, two degree-`2` vertices, and the
degree-`2` vertices are adjacent, then the original graph is `4`-colorable.

Source: new theorem realizing the adjacent branch as complement shape `P₄ ⊔ K₂ ⊔ K₁`. -/
theorem colorable_four_of_compl_zero_two_two_profile_of_adj
    {u p q : V}
    (hup : u ≠ p) (huq : u ≠ q) (hpq_ne : p ≠ q)
    (hu0 : Gᶜ.degree u = 0) (hp2 : Gᶜ.degree p = 2) (hq2 : Gᶜ.degree q = 2)
    (hrest1 : ∀ x : V, x ≠ u → x ≠ p → x ≠ q → Gᶜ.degree x = 1)
    (hpq : Gᶜ.Adj p q)
    (hcard : Fintype.card V = 7) :
    G.Colorable 4 := by
  classical
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  obtain ⟨a, haq, hpa, hp_only⟩ :=
    SimpleGraph.exists_other_neighbor_of_degree_eq_two (G := Gᶜ) hp2 hpq
  obtain ⟨b, hbp, hqb, hq_only⟩ :=
    SimpleGraph.exists_other_neighbor_of_degree_eq_two (G := Gᶜ) hq2 hpq.symm
  have hau : a ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨p, hpa.symm⟩)
  have hap : a ≠ p := Gᶜ.ne_of_adj hpa.symm
  have haq' : a ≠ q := haq
  have hbu : b ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨q, hqb.symm⟩)
  have hbp' : b ≠ p := hbp
  have hbq : b ≠ q := Gᶜ.ne_of_adj hqb.symm
  have hpu : p ≠ u := hup.symm
  have hqu : q ≠ u := huq.symm
  have hua : u ≠ a := hau.symm
  have hub : u ≠ b := hbu.symm
  have hpa' : p ≠ a := hap.symm
  have hpb : p ≠ b := hbp'.symm
  have hqa : q ≠ a := haq'.symm
  have hqb' : q ≠ b := hbq.symm
  have ha1 : Gᶜ.degree a = 1 := hrest1 a hau hap haq'
  have hb1 : Gᶜ.degree b = 1 := hrest1 b hbu hbp' hbq
  have ha_unique : ∃! x : V, Gᶜ.Adj a x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) ha1
  have hb_unique : ∃! x : V, Gᶜ.Adj b x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hb1
  have ha_only_p : ∀ x : V, Gᶜ.Adj a x → x = p := by
    intro x hax
    rcases ha_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hax
      _ = p := by symm; exact hyuniq p hpa.symm
  have hb_only_q : ∀ x : V, Gᶜ.Adj b x → x = q := by
    intro x hbx
    rcases hb_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hbx
      _ = q := by symm; exact hyuniq q hqb.symm
  have hab : a ≠ b := by
    intro hEq
    have : q = p := by
      exact ha_only_p q (by simpa [hEq] using hqb.symm)
    exact hpq_ne this.symm
  have hba : b ≠ a := by
    intro hEq
    exact hab hEq.symm
  let t : Set V := (({u, p, q, a, b} : Set V)ᶜ)
  have hcard_t : Fintype.card ↥t = 2 := by
    have hfive : Fintype.card ({u, p, q, a, b} : Set V) = 5 := by
      rw [← Set.toFinset_card]
      simp [hup, huq, hpq_ne, hua, hub, hpa', hpb, hqa, hqb', hab, hba]
    calc
      Fintype.card ↥t = Fintype.card V - Fintype.card ({u, p, q, a, b} : Set V) := by
        simpa [t] using (Fintype.card_compl_set ({u, p, q, a, b} : Set V))
      _ = 7 - 5 := by rw [hcard, hfive]
      _ = 2 := by decide
  have ht_ncard : t.ncard = 2 := by
    have hcard_eq : Fintype.card ↥t = t.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hcard_t
  obtain ⟨c, d, hcd, ht_eq⟩ := Set.ncard_eq_two.mp ht_ncard
  have hct : c ∈ t := by rw [ht_eq]; simp
  have hdt : d ∈ t := by rw [ht_eq]; simp
  have hct' : c ≠ u ∧ c ≠ p ∧ c ≠ q ∧ c ≠ a ∧ c ≠ b := by
    simpa [t, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hct
  have hdt' : d ≠ u ∧ d ≠ p ∧ d ≠ q ∧ d ≠ a ∧ d ≠ b := by
    simpa [t, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hdt
  have hcu : c ≠ u := hct'.1
  have hcp : c ≠ p := hct'.2.1
  have hcq : c ≠ q := hct'.2.2.1
  have hca : c ≠ a := hct'.2.2.2.1
  have hcb : c ≠ b := hct'.2.2.2.2
  have hdu : d ≠ u := hdt'.1
  have hdp : d ≠ p := hdt'.2.1
  have hdq : d ≠ q := hdt'.2.2.1
  have hda : d ≠ a := hdt'.2.2.2.1
  have hdb : d ≠ b := hdt'.2.2.2.2
  have huc : u ≠ c := hcu.symm
  have hud : u ≠ d := hdu.symm
  have hpc : p ≠ c := hcp.symm
  have hpd : p ≠ d := hdp.symm
  have hqc : q ≠ c := hcq.symm
  have hqd : q ≠ d := hdq.symm
  have hac : a ≠ c := hca.symm
  have had : a ≠ d := hda.symm
  have hbc : b ≠ c := hcb.symm
  have hbd : b ≠ d := hdb.symm
  have hc1 : Gᶜ.degree c = 1 := hrest1 c hcu hcp hcq
  have hd1 : Gᶜ.degree d = 1 := hrest1 d hdu hdp hdq
  have hc_unique : ∃! x : V, Gᶜ.Adj c x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hc1
  have hd_unique : ∃! x : V, Gᶜ.Adj d x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hd1
  have hcp_not : ¬ Gᶜ.Adj c p := by
    intro hcp_adj
    rcases hp_only c hcp_adj.symm with h | h
    · exact hcq h
    · exact hca h
  have hcq_not : ¬ Gᶜ.Adj c q := by
    intro hcq_adj
    rcases hq_only c hcq_adj.symm with h | h
    · exact hcp h
    · exact hcb h
  have hca_not : ¬ Gᶜ.Adj c a := by
    intro hca_adj
    exact hcp (ha_only_p c hca_adj.symm)
  have hcb_not : ¬ Gᶜ.Adj c b := by
    intro hcb_adj
    exact hcq (hb_only_q c hcb_adj.symm)
  have hcu_not : ¬ Gᶜ.Adj c u := by
    intro hcu_adj
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨c, hcu_adj.symm⟩)
  have hcd_adj : Gᶜ.Adj c d := by
    rcases hc_unique with ⟨x, hcx, hcxuniq⟩
    have hx_ne_u : x ≠ u := by
      intro hEq
      exact hcu_not (hEq ▸ hcx)
    have hx_ne_p : x ≠ p := by
      intro hEq
      exact hcp_not (hEq ▸ hcx)
    have hx_ne_q : x ≠ q := by
      intro hEq
      exact hcq_not (hEq ▸ hcx)
    have hx_ne_a : x ≠ a := by
      intro hEq
      exact hca_not (hEq ▸ hcx)
    have hx_ne_b : x ≠ b := by
      intro hEq
      exact hcb_not (hEq ▸ hcx)
    have hx_in_t : x ∈ t := by
      simp [t, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        hx_ne_u, hx_ne_p, hx_ne_q, hx_ne_a, hx_ne_b]
    rw [ht_eq] at hx_in_t
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_in_t
    rcases hx_in_t with rfl | rfl
    · exact False.elim (Gᶜ.loopless _ hcx)
    · exact hcx
  have hcover : ∀ y : V, y = u ∨ y = p ∨ y = q ∨ y = a ∨ y = b ∨ y = c ∨ y = d := by
    intro y
    by_cases hyu : y = u
    · exact Or.inl hyu
    by_cases hyp : y = p
    · exact Or.inr (Or.inl hyp)
    by_cases hyq : y = q
    · exact Or.inr (Or.inr (Or.inl hyq))
    by_cases hya : y = a
    · exact Or.inr (Or.inr (Or.inr (Or.inl hya)))
    by_cases hyb : y = b
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hyb))))
    have hyt : y ∈ t := by
      simp [t, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        hyu, hyp, hyq, hya, hyb]
    rw [ht_eq] at hyt
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hyt
    rcases hyt with hyc | hyd
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hyc)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hyd)))))
  let color : V → Fin 4 := fun x =>
    if x = u then 0 else
    if x = p ∨ x = a then 1 else
    if x = q ∨ x = b then 2 else
    3
  have hcolor_u : color u = 0 := by simp [color]
  have hcolor_p : color p = 1 := by simp [color, hpu]
  have hcolor_q : color q = 2 := by simp [color, hqu, hpq_ne.symm, hqa]
  have hcolor_a : color a = 1 := by simp [color, hau]
  have hcolor_b : color b = 2 := by simp [color, hbu, hbp', hba]
  have hcolor_c : color c = 3 := by
    simp [color, hcu, hcp, hcq, hca, hcb]
  have hcolor_d : color d = 3 := by
    simp [color, hdu, hdp, hdq, hda, hdb]
  have bucket0 {y : V} (hy : color y = 0) : y = u := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · have : False := by simpa [hcolor_p] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_q] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_c] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_d] using hy
      exact False.elim this
  have bucket1 {y : V} (hy : color y = 1) : y = p ∨ y = a := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hy
      exact False.elim this
    · exact Or.inl rfl
    · have : False := by simpa [hcolor_q] using hy
      exact False.elim this
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_b] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_c] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_d] using hy
      exact False.elim this
  have bucket2 {y : V} (hy : color y = 2) : y = q ∨ y = b := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_p] using hy
      exact False.elim this
    · exact Or.inl rfl
    · have : False := by simpa [hcolor_a] using hy
      exact False.elim this
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_c] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_d] using hy
      exact False.elim this
  have bucket3 {y : V} (hy : color y = 3) : y = c ∨ y = d := by
    rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_u] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_p] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_q] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_a] using hy
      exact False.elim this
    · have : False := by simpa [hcolor_b] using hy
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcoloring : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro y z hyz
    intro hyzEq
    by_cases hy0 : color y = 0
    · have hz0 : color z = 0 := by rw [← hyzEq, hy0]
      rw [bucket0 hy0, bucket0 hz0] at hyz
      exact G.loopless _ hyz
    · by_cases hy1 : color y = 1
      · have hz1 : color z = 1 := by rw [← hyzEq, hy1]
        rcases bucket1 hy1 with hyp' | hya'
        · subst y
          rcases bucket1 hz1 with hzp | hza
          · subst z
            exact G.loopless _ hyz
          · subst z
            exact ((SimpleGraph.compl_adj G p a).1 hpa).2 hyz
        · subst y
          rcases bucket1 hz1 with hzp | hza
          · subst z
            exact ((SimpleGraph.compl_adj G a p).1 hpa.symm).2 hyz
          · subst z
            exact G.loopless _ hyz
      · by_cases hy2 : color y = 2
        · have hz2 : color z = 2 := by rw [← hyzEq, hy2]
          rcases bucket2 hy2 with hyq' | hyb'
          · subst y
            rcases bucket2 hz2 with hzq | hzb
            · subst z
              exact G.loopless _ hyz
            · subst z
              exact ((SimpleGraph.compl_adj G q b).1 hqb).2 hyz
          · subst y
            rcases bucket2 hz2 with hzq | hzb
            · subst z
              exact ((SimpleGraph.compl_adj G b q).1 hqb.symm).2 hyz
            · subst z
              exact G.loopless _ hyz
        · have hy3 : color y = 3 := by
            rcases hcover y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact False.elim (hy0 hcolor_u)
            · exact False.elim (hy1 hcolor_p)
            · exact False.elim (hy2 hcolor_q)
            · exact False.elim (hy1 hcolor_a)
            · exact False.elim (hy2 hcolor_b)
            · exact hcolor_c
            · exact hcolor_d
          have hz3 : color z = 3 := by rw [← hyzEq, hy3]
          rcases bucket3 hy3 with hyc | hyd
          · subst y
            rcases bucket3 hz3 with hzc | hzd
            · subst z
              exact G.loopless _ hyz
            · subst z
              exact ((SimpleGraph.compl_adj G c d).1 hcd_adj).2 hyz
          · subst y
            rcases bucket3 hz3 with hzc | hzd
            · subst z
              exact ((SimpleGraph.compl_adj G d c).1 hcd_adj.symm).2 hyz
            · subst z
              exact G.loopless _ hyz
  exact hcoloring.colorable

/-- If the remaining complement profile has one isolated vertex, two degree-`2` vertices, and the
degree-`2` vertices are nonadjacent, then the original graph has a `5`-clique.

Source: new theorem realizing the nonadjacent branch as complement shape `P₃ ⊔ P₃ ⊔ K₁`. -/
theorem not_cliqueFree_of_compl_zero_two_two_profile_of_not_adj
    {u p q : V}
    (hup : u ≠ p) (huq : u ≠ q) (hpq_ne : p ≠ q)
    (hu0 : Gᶜ.degree u = 0) (hp2 : Gᶜ.degree p = 2) (hq2 : Gᶜ.degree q = 2)
    (hrest1 : ∀ x : V, x ≠ u → x ≠ p → x ≠ q → Gᶜ.degree x = 1)
    (hpq_not : ¬ Gᶜ.Adj p q) :
    ¬ G.CliqueFree 5 := by
  classical
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  obtain ⟨a, b, hab, hp_neigh⟩ := Set.ncard_eq_two.mp <| by
    have hcard : Fintype.card ↥(Gᶜ.neighborSet p) = 2 := by
      simpa [hp2] using (Gᶜ.card_neighborSet_eq_degree (v := p))
    have hcard_eq : Fintype.card ↥(Gᶜ.neighborSet p) = (Gᶜ.neighborSet p).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hcard
  obtain ⟨c, d, hcd, hq_neigh⟩ := Set.ncard_eq_two.mp <| by
    have hcard : Fintype.card ↥(Gᶜ.neighborSet q) = 2 := by
      simpa [hq2] using (Gᶜ.card_neighborSet_eq_degree (v := q))
    have hcard_eq : Fintype.card ↥(Gᶜ.neighborSet q) = (Gᶜ.neighborSet q).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hcard
  have hp_a : Gᶜ.Adj p a := by
    have : a ∈ Gᶜ.neighborSet p := by rw [hp_neigh]; simp
    simpa [SimpleGraph.mem_neighborSet] using this
  have hp_b : Gᶜ.Adj p b := by
    have : b ∈ Gᶜ.neighborSet p := by rw [hp_neigh]; simp
    simpa [SimpleGraph.mem_neighborSet] using this
  have hq_c : Gᶜ.Adj q c := by
    have : c ∈ Gᶜ.neighborSet q := by rw [hq_neigh]; simp
    simpa [SimpleGraph.mem_neighborSet] using this
  have hq_d : Gᶜ.Adj q d := by
    have : d ∈ Gᶜ.neighborSet q := by rw [hq_neigh]; simp
    simpa [SimpleGraph.mem_neighborSet] using this
  have hau : a ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨p, hp_a.symm⟩)
  have hap : a ≠ p := Gᶜ.ne_of_adj hp_a.symm
  have haq : a ≠ q := by
    intro hEq
    exact hpq_not (hEq ▸ hp_a)
  have hbu : b ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨p, hp_b.symm⟩)
  have hbp : b ≠ p := Gᶜ.ne_of_adj hp_b.symm
  have hbq : b ≠ q := by
    intro hEq
    exact hpq_not (hEq ▸ hp_b)
  have hcu : c ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨q, hq_c.symm⟩)
  have hcp : c ≠ p := by
    intro hEq
    exact hpq_not (hEq ▸ hq_c.symm)
  have hcq : c ≠ q := Gᶜ.ne_of_adj hq_c.symm
  have hdu : d ≠ u := by
    intro hEq
    exact hu_not_mem (hEq ▸ (SimpleGraph.mem_support (G := Gᶜ)).2 ⟨q, hq_d.symm⟩)
  have hdp : d ≠ p := by
    intro hEq
    exact hpq_not (hEq ▸ hq_d.symm)
  have hdq : d ≠ q := Gᶜ.ne_of_adj hq_d.symm
  have ha1 : Gᶜ.degree a = 1 := hrest1 a hau hap haq
  have hb1 : Gᶜ.degree b = 1 := hrest1 b hbu hbp hbq
  have hc1 : Gᶜ.degree c = 1 := hrest1 c hcu hcp hcq
  have hd1 : Gᶜ.degree d = 1 := hrest1 d hdu hdp hdq
  have ha_unique : ∃! x : V, Gᶜ.Adj a x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) ha1
  have hb_unique : ∃! x : V, Gᶜ.Adj b x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hb1
  have hc_unique : ∃! x : V, Gᶜ.Adj c x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hc1
  have hd_unique : ∃! x : V, Gᶜ.Adj d x := SimpleGraph.existsUnique_adj_of_degree_eq_one (G := Gᶜ) hd1
  have ha_only_p : ∀ x : V, Gᶜ.Adj a x → x = p := by
    intro x hax
    rcases ha_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hax
      _ = p := by symm; exact hyuniq p hp_a.symm
  have hb_only_p : ∀ x : V, Gᶜ.Adj b x → x = p := by
    intro x hbx
    rcases hb_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hbx
      _ = p := by symm; exact hyuniq p hp_b.symm
  have hc_only_q : ∀ x : V, Gᶜ.Adj c x → x = q := by
    intro x hcx
    rcases hc_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hcx
      _ = q := by symm; exact hyuniq q hq_c.symm
  have hd_only_q : ∀ x : V, Gᶜ.Adj d x → x = q := by
    intro x hdx
    rcases hd_unique with ⟨y, hy, hyuniq⟩
    calc
      x = y := hyuniq x hdx
      _ = q := by symm; exact hyuniq q hq_d.symm
  have hac_ne : a ≠ c := by
    intro hEq
    have : q = p := ha_only_p q (by simpa [hEq] using hq_c.symm)
    exact hpq_ne this.symm
  have had_ne : a ≠ d := by
    intro hEq
    have : q = p := ha_only_p q (by simpa [hEq] using hq_d.symm)
    exact hpq_ne this.symm
  have hbc_ne : b ≠ c := by
    intro hEq
    have : q = p := hb_only_p q (by simpa [hEq] using hq_c.symm)
    exact hpq_ne this.symm
  have hbd_ne : b ≠ d := by
    intro hEq
    have : q = p := hb_only_p q (by simpa [hEq] using hq_d.symm)
    exact hpq_ne this.symm
  have hac : ¬ Gᶜ.Adj a c := by
    intro hac
    exact hcp (ha_only_p c hac)
  have had : ¬ Gᶜ.Adj a d := by
    intro had
    exact hdp (ha_only_p d had)
  have hbc : ¬ Gᶜ.Adj b c := by
    intro hbc
    exact hcp (hb_only_p c hbc)
  have hbd : ¬ Gᶜ.Adj b d := by
    intro hbd
    exact hdp (hb_only_p d hbd)
  have hab_not : ¬ Gᶜ.Adj a b := by
    intro hab'
    exact hbp (ha_only_p b hab')
  have hcd_not : ¬ Gᶜ.Adj c d := by
    intro hcd'
    exact hdq (hc_only_q d hcd')
  have huaG : G.Adj u a := by
    by_contra hua
    have huaC : Gᶜ.Adj u a := (SimpleGraph.compl_adj G u a).2 ⟨hau.symm, hua⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨a, huaC⟩)
  have hubG : G.Adj u b := by
    by_contra hub
    have hubC : Gᶜ.Adj u b := (SimpleGraph.compl_adj G u b).2 ⟨hbu.symm, hub⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨b, hubC⟩)
  have hucG : G.Adj u c := by
    by_contra huc
    have hucC : Gᶜ.Adj u c := (SimpleGraph.compl_adj G u c).2 ⟨hcu.symm, huc⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨c, hucC⟩)
  have hudG : G.Adj u d := by
    by_contra hud
    have hudC : Gᶜ.Adj u d := (SimpleGraph.compl_adj G u d).2 ⟨hdu.symm, hud⟩
    exact hu_not_mem ((SimpleGraph.mem_support (G := Gᶜ)).2 ⟨d, hudC⟩)
  have habG : G.Adj a b := by
    by_contra habG
    exact hab_not ((SimpleGraph.compl_adj G a b).2 ⟨by
      intro hEq
      exact hab hEq, habG⟩)
  have hacG : G.Adj a c := by
    by_contra hacG
    exact hac ((SimpleGraph.compl_adj G a c).2 ⟨by
      intro hEq
      exact hac_ne hEq, hacG⟩)
  have hadG : G.Adj a d := by
    by_contra hadG
    exact had ((SimpleGraph.compl_adj G a d).2 ⟨by
      intro hEq
      exact had_ne hEq, hadG⟩)
  have hbcG : G.Adj b c := by
    by_contra hbcG
    exact hbc ((SimpleGraph.compl_adj G b c).2 ⟨by
      intro hEq
      exact hbc_ne hEq, hbcG⟩)
  have hbdG : G.Adj b d := by
    by_contra hbdG
    exact hbd ((SimpleGraph.compl_adj G b d).2 ⟨by
      intro hEq
      exact hbd_ne hEq, hbdG⟩)
  have hcdG : G.Adj c d := by
    by_contra hcdG
    exact hcd_not ((SimpleGraph.compl_adj G c d).2 ⟨by
      intro hEq
      exact hcd hEq, hcdG⟩)
  let s : Finset V := {u, a, b, c, d}
  have hsClique : G.IsClique s := by
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    simp [s] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl
    all_goals
      first
        | contradiction
        | exact huaG
        | exact huaG.symm
        | exact hubG
        | exact hubG.symm
        | exact hucG
        | exact hucG.symm
        | exact hudG
        | exact hudG.symm
        | exact habG
        | exact habG.symm
        | exact hacG
        | exact hacG.symm
        | exact hadG
        | exact hadG.symm
        | exact hbcG
        | exact hbcG.symm
        | exact hbdG
        | exact hbdG.symm
        | exact hcdG
        | exact hcdG.symm
  have hsCard : s.card = 5 := by
    simp [s, hau.symm, hbu.symm, hcu.symm, hdu.symm, hab, hac_ne, had_ne, hbc_ne, hbd_ne, hcd]
  have hsNClique : G.IsNClique 5 s := by
    rw [SimpleGraph.isNClique_iff]
    exact ⟨hsClique, hsCard⟩
  exact hsNClique.not_cliqueFree

/-- Under `K₅`-freeness, the `(2,4,1)` degree-count profile cannot occur in the seven-vertex
`|E| = 17` branch.

Source: new theorem closing the second remaining seven-vertex `17`-edge profile by splitting its
complement geometry into an explicit coloring branch and a direct `K₅` branch. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 2 ∧ d5 = 4 ∧ d6 = 1) := by
  intro hprof
  rcases h.exists_distinct_compl_degree_zero_two_two_forall_rest_degree_one_of_profile_two_four_one
      hcard hedge hprof with
    ⟨u, p, q, hup, huq, hpq_ne, hu0, hp2, hq2, hrest1⟩
  by_cases hpq : Gᶜ.Adj p q
  · exact h.not_colorable
      (colorable_four_of_compl_zero_two_two_profile_of_adj
        (G := G) hup huq hpq_ne hu0 hp2 hq2 hrest1 hpq hcard)
  · exact
      (not_cliqueFree_of_compl_zero_two_two_profile_of_not_adj
        (G := G) hup huq hpq_ne hu0 hp2 hq2 hrest1 hpq) hfree

/-- Under `K₅`-freeness, the seven-vertex `|E| = 17` degree-count split reduces to the single
profile `(3,2,2)`.

Source: new theorem excluding the `(2,4,1)` profile after the previous elimination of `(1,6,0)`
and `(4,0,3)`. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 3 ∧ d5 = 2 ∧ d6 = 2 := by
  rcases h.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge with hcase | hcase
  · exfalso
    exact
      (h.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
        hcard hfree hedge) hcase
  · exact hcase

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift excluding the `(2,4,1)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 2 ∧ d5 = 4 ∧ d6 = 1) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

/-- Vertex-critical lift of the thrice-reduced seven-vertex `17`-edge degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 3 ∧ d5 = 2 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift excluding the `(2,4,1)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 2 ∧ d5 = 4 ∧ d6 = 1) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift of the thrice-reduced seven-vertex `17`-edge degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 3 ∧ d5 = 2 ∧ d6 = 2 := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift excluding the `(2,4,1)` seven-vertex `17`-edge profile under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 2 ∧ d5 = 4 ∧ d6 = 1) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_profile_ne_two_four_one_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

/-- Minimal-counterexample lift of the thrice-reduced seven-vertex `17`-edge degree-count split
under `K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    d4 = 3 ∧ d5 = 2 ∧ d6 = 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_case_split_reduced_thrice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

end MinimalBridge

end FourColor.Curriculum.Actual
