import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Matching
import FourColor.Curriculum.Actual.SevenVertexSeventeenComplement

namespace FourColor.Curriculum.Actual

section MatchingHelpers

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

/-- A finite `1`-regular graph is a perfect matching on its full vertex set.

Source: helper theorem for the rigid `(1,6,0)` branch in the seven-vertex `17`-edge frontier. -/
theorem SimpleGraph.top_isPerfectMatching_of_isRegularOfDegree_one
    (hreg : G.IsRegularOfDegree 1) :
    (⊤ : SimpleGraph.Subgraph G).IsPerfectMatching := by
  letI : DecidableRel (⊤ : SimpleGraph.Subgraph G).Adj := by
    intro u v
    change Decidable (G.Adj u v)
    infer_instance
  letI : ∀ v : V, Fintype ↑((⊤ : SimpleGraph.Subgraph G).neighborSet v) := fun v =>
    SimpleGraph.Subgraph.finiteAt
      (G := G) (G' := (⊤ : SimpleGraph.Subgraph G)) ⟨v, by simp⟩
  letI : ∀ v : V, Fintype ↑((⊤ : SimpleGraph.Subgraph G).spanningCoe.neighborSet v) := fun v =>
    by simpa [SimpleGraph.Subgraph.spanningCoe_top] using
      (inferInstance : Fintype ↑(G.neighborSet v))
  refine (SimpleGraph.Subgraph.isPerfectMatching_iff
    (M := (⊤ : SimpleGraph.Subgraph G))).2 ?_
  intro v
  have hdeg : G.degree v = 1 := hreg v
  have hsubdeg : (⊤ : SimpleGraph.Subgraph G).degree v = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe
      (G' := (⊤ : SimpleGraph.Subgraph G)) (v := v)]
    simpa [SimpleGraph.Subgraph.spanningCoe_top] using hdeg
  exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj
    (G' := (⊤ : SimpleGraph.Subgraph G)) (v := v)).mp hsubdeg

end MatchingHelpers

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The `(1,6,0)` degree-count profile in the seven-vertex `|E| = 17` branch forces a rigid
complement decomposition: one `2`-valent center, two adjacent leaves, and a `1`-regular induced
graph on the remaining four vertices.

Source: new theorem translating the exact degree profile into complement structure before the
explicit coloring step. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_compl_adj_card_four_and_induce_isRegularOfDegree_one_of_profile_one_six_zero
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) :
    ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      Gᶜ.Adj u v ∧ Gᶜ.Adj u w ∧
      Gᶜ.degree u = 2 ∧ Gᶜ.degree v = 1 ∧ Gᶜ.degree w = 1 ∧
      Fintype.card ↥((({u, v, w} : Set V)ᶜ)) = 4 ∧
      ((Gᶜ).induce (({u, v, w} : Set V)ᶜ)).IsRegularOfDegree 1 := by
  classical
  let s4 : Finset V := Finset.univ.filter fun x : V => G.degree x = 4
  let s6 : Finset V := Finset.univ.filter fun x : V => G.degree x = 6
  rcases hprof with ⟨hd4, _hd5, hd6⟩
  have hs4 : s4.card = 1 := by
    simpa [s4] using hd4
  have hs6 : s6.card = 0 := by
    simpa [s6] using hd6
  rcases Finset.card_eq_one.mp hs4 with ⟨u, hs4eq⟩
  have hu4 : G.degree u = 4 := by
    have humem : u ∈ s4 := by
      rw [hs4eq]
      simp
    exact (Finset.mem_filter.mp humem).2
  have hs6empty : s6 = ∅ := Finset.card_eq_zero.mp hs6
  have hrest5 : ∀ x : V, x ≠ u → G.degree x = 5 := by
    intro x hxu
    rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
        hcard hedge x with hx4 | hx5 | hx6
    · have hxmem : x ∈ s4 := by simp [s4, hx4]
      rw [hs4eq] at hxmem
      simp [hxu] at hxmem
    · exact hx5
    · have hxmem : x ∈ s6 := by simp [s6, hx6]
      rw [hs6empty] at hxmem
      simp at hxmem
  have hu2 : Gᶜ.degree u = 2 := by
    simpa [hcard, hu4] using (SimpleGraph.degree_compl (G := G) (v := u))
  have hrest1 : ∀ x : V, x ≠ u → Gᶜ.degree x = 1 := by
    intro x hxu
    simpa [hcard, hrest5 x hxu] using (SimpleGraph.degree_compl (G := G) (v := x))
  have hneigh_card : Fintype.card ↥(Gᶜ.neighborSet u) = 2 := by
    simpa [hu2] using (Gᶜ.card_neighborSet_eq_degree (v := u))
  have hneigh_ncard : (Gᶜ.neighborSet u).ncard = 2 := by
    have hcard_eq : Fintype.card ↥(Gᶜ.neighborSet u) = (Gᶜ.neighborSet u).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hneigh_card
  obtain ⟨v, w, hvw, hneigh_eq⟩ := Set.ncard_eq_two.mp hneigh_ncard
  have huv : Gᶜ.Adj u v := by
    have hmem : v ∈ Gᶜ.neighborSet u := by
      rw [hneigh_eq]
      simp
    simpa [SimpleGraph.mem_neighborSet] using hmem
  have huw : Gᶜ.Adj u w := by
    have hmem : w ∈ Gᶜ.neighborSet u := by
      rw [hneigh_eq]
      simp
    simpa [SimpleGraph.mem_neighborSet] using hmem
  have huv' : u ≠ v := Gᶜ.ne_of_adj huv
  have huw' : u ≠ w := Gᶜ.ne_of_adj huw
  have hv1 : Gᶜ.degree v = 1 := hrest1 v huv'.symm
  have hw1 : Gᶜ.degree w = 1 := hrest1 w huw'.symm
  let M : SimpleGraph.Subgraph Gᶜ := ⊤
  letI : DecidableRel M.Adj := by
    intro a b
    change Decidable (Gᶜ.Adj a b)
    infer_instance
  letI : ∀ x : V, Fintype ↑(M.neighborSet x) := fun x =>
    SimpleGraph.Subgraph.finiteAt
      (G := Gᶜ) (G' := M) ⟨x, by simp [M]⟩
  letI : ∀ x : V, Fintype ↑(M.spanningCoe.neighborSet x) := fun x =>
    by simpa [M, SimpleGraph.Subgraph.spanningCoe_top] using
      (inferInstance : Fintype ↑(Gᶜ.neighborSet x))
  have hvMdeg : M.degree v = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe (G' := M) (v := v)]
    simpa [M, SimpleGraph.Subgraph.spanningCoe_top] using hv1
  have hwMdeg : M.degree w = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe (G' := M) (v := w)]
    simpa [M, SimpleGraph.Subgraph.spanningCoe_top] using hw1
  have hv_unique : ∃! x : V, M.Adj v x := by
    exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj (G' := M) (v := v)).mp hvMdeg
  have hw_unique : ∃! x : V, M.Adj w x := by
    exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj (G' := M) (v := w)).mp hwMdeg
  rcases hv_unique with ⟨xv, hxv_adj, hxv_unique⟩
  rcases hw_unique with ⟨xw, hxw_adj, hxw_unique⟩
  have hxv_eq_u : xv = u := by
    exact (hxv_unique u (by simpa [M] using huv.symm)).symm
  have hxw_eq_u : xw = u := by
    exact (hxw_unique u (by simpa [M] using huw.symm)).symm
  have hv_only_u : ∀ x : V, Gᶜ.Adj v x → x = u := by
    intro x hvx
    calc
      x = xv := hxv_unique x (by simpa [M] using hvx)
      _ = u := hxv_eq_u
  have hw_only_u : ∀ x : V, Gᶜ.Adj w x → x = u := by
    intro x hwx
    calc
      x = xw := hxw_unique x (by simpa [M] using hwx)
      _ = u := hxw_eq_u
  have hu_only_vw : ∀ x : V, Gᶜ.Adj u x → x = v ∨ x = w := by
    intro x hux
    have hmem : x ∈ Gᶜ.neighborSet u := by
      simpa [SimpleGraph.mem_neighborSet] using hux
    rw [hneigh_eq] at hmem
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have htriple_card : Fintype.card ({u, v, w} : Set V) = 3 := by
    rw [← Set.toFinset_card]
    simp [huv', huw', hvw]
  have hcard_rest : Fintype.card ↥((({u, v, w} : Set V)ᶜ)) = 4 := by
    calc
      Fintype.card ↥((({u, v, w} : Set V)ᶜ))
          = Fintype.card V - Fintype.card ({u, v, w} : Set V) := by
              simpa using (Fintype.card_compl_set ({u, v, w} : Set V))
      _ = 7 - 3 := by rw [hcard, htriple_card]
      _ = 4 := by decide
  have hreg_rest : ((Gᶜ).induce (({u, v, w} : Set V)ᶜ)).IsRegularOfDegree 1 := by
    intro x
    have hxu : (x : V) ≠ u := by
      intro hEq
      have hx : (x : V) ∈ (({u, v, w} : Set V)ᶜ) := x.property
      simp [hEq] at hx
    have hxv : (x : V) ≠ v := by
      intro hEq
      have hx : (x : V) ∈ (({u, v, w} : Set V)ᶜ) := x.property
      simp [hEq] at hx
    have hxw : (x : V) ≠ w := by
      intro hEq
      have hx : (x : V) ∈ (({u, v, w} : Set V)ᶜ) := x.property
      simp [hEq] at hx
    have hsubset : Gᶜ.neighborSet x ⊆ (({u, v, w} : Set V)ᶜ) := by
      intro y hy
      have hxy : Gᶜ.Adj (x : V) y := by
        simpa [SimpleGraph.mem_neighborSet] using hy
      have hyu : y ≠ u := by
        intro hyu
        rcases hu_only_vw (x := x) (by simpa [hyu] using hxy.symm) with h | h
        · exact hxv h
        · exact hxw h
      have hyv : y ≠ v := by
        intro hyv
        exact hxu (hv_only_u (x := x) (by simpa [hyv] using hxy.symm))
      have hyw : y ≠ w := by
        intro hyw
        exact hxu (hw_only_u (x := x) (by simpa [hyw] using hxy.symm))
      simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hyu, hyv, hyw]
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hsubset]
    exact hrest1 x hxu
  exact ⟨u, v, w, huv', huw', hvw, huv, huw, hu2, hv1, hw1, hcard_rest, hreg_rest⟩

/-- The `(1,6,0)` degree-count profile in the seven-vertex `|E| = 17` branch is `4`-colorable.

Source: new theorem coloring the forced complement shape by one leaf-center pair, one singleton
leaf, and the two edges of the residual perfect matching. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_profile_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 17)
    (hprof :
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) :
    G.Colorable 4 := by
  classical
  rcases h.exists_distinct_compl_adj_card_four_and_induce_isRegularOfDegree_one_of_profile_one_six_zero
      hcard hedge hprof with
    ⟨u, v, w, huv, huw, hvw, huvC, huwC, hu2, hv1, hw1, hcard_rest, hreg_rest⟩
  let t : Set V := (({u, v, w} : Set V)ᶜ)
  let H : SimpleGraph t := (Gᶜ).induce t
  let M : SimpleGraph.Subgraph H := ⊤
  letI : DecidableRel H.Adj := inferInstance
  letI : DecidableRel M.Adj := by
    intro a b
    change Decidable (H.Adj a b)
    infer_instance
  letI : Fintype M.edgeSet := by
    dsimp [M]
    infer_instance
  let hM : M.IsPerfectMatching := by
    simpa [H, M] using
      (SimpleGraph.top_isPerfectMatching_of_isRegularOfDegree_one (G := H) hreg_rest)
  have huw' : w ≠ u := huw.symm
  have hwv' : w ≠ v := hvw.symm
  let restVertex : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → t := fun x hxu hxv hxw =>
    ⟨x, by
      simp [t, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxu, hxv, hxw]⟩
  let matchedColor : ∀ x : V, x ≠ u → x ≠ v → x ≠ w → M.edgeSet := fun x hxu hxv hxw =>
    hM.1.toEdge ⟨restVertex x hxu hxv hxw, hM.2 (restVertex x hxu hxv hxw)⟩
  let color : V → Option (Option M.edgeSet) := fun x =>
    if hxw : x = w then none
    else if hxuv : x = u ∨ x = v then some none
    else some (some (matchedColor x
      (by intro hEq; exact hxuv (Or.inl hEq))
      (by intro hEq; exact hxuv (Or.inr hEq)) hxw))
  have color_eq_none_iff {x : V} : color x = none ↔ x = w := by
    constructor
    · intro hx
      by_cases hxw : x = w
      · exact hxw
      · by_cases hxuv : x = u ∨ x = v
        · simp [color, hxw, hxuv] at hx
        · simp [color, hxw, hxuv] at hx
    · intro hxw
      simp [color, hxw]
  have color_eq_some_none_iff {x : V} : color x = some none ↔ x = u ∨ x = v := by
    constructor
    · intro hx
      by_cases hxw : x = w
      · simp [color, hxw] at hx
      · by_cases hxuv : x = u ∨ x = v
        · exact hxuv
        · simp [color, hxw, hxuv] at hx
    · intro hxuv
      have hxw : x ≠ w := by
        intro hxw
        rcases hxuv with hxu | hxv
        · exact huw' (hxw.symm.trans hxu)
        · exact hwv' (hxw.symm.trans hxv)
      simp [color, hxw, hxuv]
  have hHdeg : ∀ x : t, H.degree x = 1 := hreg_rest
  have hsum : ∑ x : t, H.degree x = 4 := by
    calc
      ∑ x : t, H.degree x = ∑ _ : t, 1 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hHdeg x
      _ = Fintype.card t := by simp
      _ = 4 := by simpa [t] using hcard_rest
  have htwice : 2 * H.edgeFinset.card = 4 := by
    rw [← H.sum_degrees_eq_twice_card_edges, hsum]
  have hedge_H : H.edgeFinset.card = 2 := by
    have hdiv := congrArg (fun n : Nat => n / 2) htwice
    simpa using hdiv
  have hcard_colors : Fintype.card M.edgeSet = 2 := by
    simpa [M, SimpleGraph.Subgraph.edgeSet_top] using (H.edgeFinset_card).symm.trans hedge_H
  have hcolor : G.Coloring (Option (Option M.edgeSet)) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro a b hab
    have hne : a ≠ b := G.ne_of_adj hab
    intro hEq
    by_cases haw : a = w
    · have hbw : b ≠ w := by
        intro hEq'
        exact hne (haw.trans hEq'.symm)
      have ha_none : color a = none := by simp [color, haw]
      have hb_none : color b = none := hEq.symm.trans ha_none
      exact hbw (color_eq_none_iff.mp hb_none)
    by_cases hauv : a = u ∨ a = v
    · have hbw : b ≠ w := by
        intro hEq'
        have hbwv : b = u ∨ b = v := by
          exact color_eq_some_none_iff.mp (hEq.symm.trans (by simp [color, haw, hauv]))
        rcases hbwv with hbu | hbv
        · exact huw' (hEq'.symm.trans hbu)
        · exact hwv' (hEq'.symm.trans hbv)
      have ha_pair : color a = some none := by
        simp [color, haw, hauv]
      have hb_pair : color b = some none := hEq.symm.trans ha_pair
      have hbuv : b = u ∨ b = v := color_eq_some_none_iff.mp hb_pair
      rcases hauv with hau | hav
      · rcases hbuv with hbu | hbv
        · exact hne (hau.trans hbu.symm)
        · exact ((SimpleGraph.compl_adj G u v).1 huvC).2 (by simpa [hau, hbv] using hab)
      · rcases hbuv with hbu | hbv
        · exact ((SimpleGraph.compl_adj G v u).1 huvC.symm).2 (by simpa [hav, hbu] using hab)
        · exact hne (hav.trans hbv.symm)
    have hbw : b ≠ w := by
      intro hEq'
      have ha_none : color a = none := by simp [color, hEq', hEq]
      exact haw (color_eq_none_iff.mp ha_none)
    have hbuv : ¬ (b = u ∨ b = v) := by
      intro hbuv
      have hb_pair : color b = some none := by simp [color, hbw, hbuv]
      exact hauv (color_eq_some_none_iff.mp (hEq.trans hb_pair))
    have ha_color :
        color a = some (some (matchedColor a
          (by intro hEq'; exact hauv (Or.inl hEq'))
          (by intro hEq'; exact hauv (Or.inr hEq')) haw)) := by
      simp [color, haw, hauv]
    have hb_color :
        color b = some (some (matchedColor b
          (by intro hEq'; exact hbuv (Or.inl hEq'))
          (by intro hEq'; exact hbuv (Or.inr hEq')) hbw)) := by
      simp [color, hbw, hbuv]
    rw [ha_color, hb_color] at hEq
    have hEqColor :
        matchedColor a
            (by intro hEq'; exact hauv (Or.inl hEq'))
            (by intro hEq'; exact hauv (Or.inr hEq')) haw =
          matchedColor b
            (by intro hEq'; exact hbuv (Or.inl hEq'))
            (by intro hEq'; exact hbuv (Or.inr hEq')) hbw := by
      exact Option.some.inj (Option.some.inj hEq)
    let a' : t := restVertex a
      (by intro hEq'; exact hauv (Or.inl hEq'))
      (by intro hEq'; exact hauv (Or.inr hEq')) haw
    let b' : t := restVertex b
      (by intro hEq'; exact hbuv (Or.inl hEq'))
      (by intro hEq'; exact hbuv (Or.inr hEq')) hbw
    rcases
        SimpleGraph.Subgraph.IsMatching.eq_or_adj_of_toEdge_eq hM.1 (hM.2 a') (hM.2 b')
          hEqColor with
      hab_eq | hAdj
    · exact hne (congrArg Subtype.val hab_eq)
    · have hComp : Gᶜ.Adj a b := by
        simpa [H, M, a', b'] using hAdj
      exact ((SimpleGraph.compl_adj G a b).1 hComp).2 hab
  simpa [Fintype.card_option, hcard_colors] using hcolor.colorable

/-- Under `K₅`-freeness, the `(1,6,0)` profile cannot occur in the seven-vertex `17`-edge
branch.

Source: new theorem excluding the first remaining `17`-edge profile by explicit `4`-coloring. -/
theorem IsIncidenceCriticalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (_hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) := by
  intro hprof
  exact h.not_colorable
    (h.colorable_four_of_profile_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen
      hcard hedge hprof)

/-- Under `K₅`-freeness, the seven-vertex `|E| = 17` degree-count split reduces to the two
profiles `(2,4,1)` and `(3,2,2)`.

Source: new theorem excluding the `(1,6,0)` profile after the previous exclusion of `(4,0,3)`. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  rcases h.degree_count_case_split_reduced_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge with hcase | hcase | hcase
  · exfalso
    exact
      (h.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
        hcard hfree hedge) hcase
  · exact Or.inl hcase
  · exact Or.inr hcase

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift excluding the `(1,6,0)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsVertexCriticalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

/-- Vertex-critical lift of the twice-reduced seven-vertex `17`-edge degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical_four) hcard hfree hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift excluding the `(1,6,0)` seven-vertex `17`-edge profile under
`K₅`-freeness. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift of the twice-reduced seven-vertex `17`-edge degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  exact
    IsIncidenceCriticalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      (G := G) (h := h.toIncidenceCritical hadj) hcard hfree hedge

/-- Minimal-counterexample lift excluding the `(1,6,0)` seven-vertex `17`-edge profile under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    ¬ (
      let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
      let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
      let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
      d4 = 1 ∧ d5 = 6 ∧ d6 = 0) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_profile_ne_one_six_zero_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

/-- Minimal-counterexample lift of the twice-reduced seven-vertex `17`-edge degree-count split
under `K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 17) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 2 ∧ d5 = 4 ∧ d6 = 1) ∨
      (d4 = 3 ∧ d5 = 2 ∧ d6 = 2) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.degree_count_case_split_reduced_twice_of_card_eq_seven_of_card_edgeFinset_eq_seventeen_of_cliqueFree
      hcard hfree hedge

end MinimalBridge

end FourColor.Curriculum.Actual
