import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Option
import FourColor.Curriculum.Actual.SixVertexComplement

namespace FourColor.Curriculum.Actual

section MatchingHelpers

variable {V : Type*} {G : SimpleGraph V} {M : SimpleGraph.Subgraph G}

/-- If two vertices of a matching are assigned the same matched edge, then they are equal or
adjacent in the matching.

Source: new helper lemma unpacking equality of `toEdge` values in a matching. -/
theorem SimpleGraph.Subgraph.IsMatching.eq_or_adj_of_toEdge_eq
    (hM : M.IsMatching) {u v : V} (hu : u ∈ M.verts) (hv : v ∈ M.verts)
    (hEq : hM.toEdge ⟨u, hu⟩ = hM.toEdge ⟨v, hv⟩) :
    u = v ∨ M.Adj u v := by
  let wu := (hM hu).choose
  let wv := (hM hv).choose
  have hu_adj : M.Adj u wu := (hM hu).choose_spec.1
  have hEqEdge : s(u, wu) = s(v, wv) := by
    simpa [SimpleGraph.Subgraph.IsMatching.toEdge, wu, wv] using congrArg Subtype.val hEq
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hEqEdge
  rcases hEqEdge with ⟨huv, _⟩ | ⟨_, hwuv⟩
  · exact Or.inl huv
  · exact Or.inr (by simpa [wu, wv, hwuv] using hu_adj)

end MatchingHelpers

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the six-vertex `K₅`-free `|E| = 12` branch, the graph is `4`-colorable.

Source: new theorem coloring each vertex by the complement matching edge it belongs to, with one
unused spare color. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_card_eq_six_of_card_edgeFinset_eq_twelve
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) :
    G.Colorable 4 := by
  classical
  let M : SimpleGraph.Subgraph Gᶜ := ⊤
  letI : DecidableRel M.Adj := by
    intro u v
    change Decidable (Gᶜ.Adj u v)
    infer_instance
  letI : Fintype M.edgeSet := by
    dsimp [M]
    infer_instance
  let hM : M.IsPerfectMatching := by
    simpa [M] using
      h.compl_top_isPerfectMatching_of_card_edgeFinset_eq_twelve hcard hfree hedge
  let matchedColor : V → M.edgeSet := fun v =>
    hM.1.toEdge ⟨v, hM.2 v⟩
  have hcolor : G.Coloring (Option M.edgeSet) := by
    refine SimpleGraph.Coloring.mk (fun v => some (matchedColor v)) ?_
    intro u v huv
    simp [matchedColor]
    intro hEq
    rcases
        SimpleGraph.Subgraph.IsMatching.eq_or_adj_of_toEdge_eq hM.1 (hM.2 u) (hM.2 v) hEq with
      rfl | hAdj
    · exact (G.ne_of_adj huv) rfl
    · exact ((SimpleGraph.compl_adj G u v).1 (show Gᶜ.Adj u v from hAdj)).2 huv
  have hsum : ∑ v : V, Gᶜ.degree v = 6 := by
    calc
      ∑ v : V, Gᶜ.degree v = ∑ _ : V, 1 := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact h.compl_isRegularOfDegree_one_of_card_edgeFinset_eq_twelve hcard hfree hedge v
      _ = 6 := by simp [hcard]
  have htwice : 2 * Gᶜ.edgeFinset.card = 6 := by
    rw [← Gᶜ.sum_degrees_eq_twice_card_edges, hsum]
  have hedge_compl : Gᶜ.edgeFinset.card = 3 := by
    have hdiv := congrArg (fun n : Nat => n / 2) htwice
    simpa using hdiv
  have hcard_colors : Fintype.card M.edgeSet = 3 := by
    simpa [M, SimpleGraph.Subgraph.edgeSet_top] using (Gᶜ.edgeFinset_card).symm.trans hedge_compl
  simpa [Fintype.card_option, hcard_colors] using hcolor.colorable

/-- In the six-vertex `K₅`-free `|E| = 13` branch, the graph is `4`-colorable.

Source: new theorem coloring the two complement-isolated vertices with two singleton colors and
coloring every remaining vertex by its matched complement-support edge. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_card_eq_six_of_card_edgeFinset_eq_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    G.Colorable 4 := by
  classical
  rcases h.exists_distinct_compl_degree_eq_zero_forall_compl_degree_eq_one_of_card_edgeFinset_eq_thirteen
      hcard hfree hedge with ⟨u, v, huv, hu0, hv0, hrest⟩
  let H : SimpleGraph (Gᶜ.support) := (Gᶜ).induce (Gᶜ.support)
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
      h.compl_induce_support_top_isPerfectMatching_of_card_edgeFinset_eq_thirteen hcard hfree hedge
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hv_not_mem : v ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := v)).mp hv0
  have hvu : v ≠ u := by
    intro hEq
    exact huv hEq.symm
  let supportVertex : ∀ w : V, w ≠ u → w ≠ v → Gᶜ.support := fun w hwu hwv =>
    ⟨w, (Gᶜ.degree_pos_iff_mem_support w).1 (by simp [hrest w hwu hwv])⟩
  let matchedColor : ∀ w : V, w ≠ u → w ≠ v → M.edgeSet := fun w hwu hwv =>
    hM.1.toEdge ⟨supportVertex w hwu hwv, hM.2 (supportVertex w hwu hwv)⟩
  let color : V → Option (Option M.edgeSet) := fun w =>
    if hwu : w = u then none
    else if hwv : w = v then some none
    else some (some (matchedColor w hwu hwv))
  have color_eq_none_iff {w : V} : color w = none ↔ w = u := by
    constructor
    · intro hw
      by_cases hwu : w = u
      · exact hwu
      · by_cases hwv : w = v
        · exact False.elim (by simp [color, hwv, hvu] at hw)
        · simp [color, hwu, hwv] at hw
    · intro hwu
      simp [color, hwu]
  have color_eq_some_none_iff {w : V} : color w = some none ↔ w = v := by
    constructor
    · intro hw
      by_cases hwu : w = u
      · simp [color, hwu] at hw
      · by_cases hwv : w = v
        · exact hwv
        · simp [color, hwu, hwv] at hw
    · intro hwv
      by_cases hwu : w = u
      · exact False.elim (huv (hwu.symm.trans hwv))
      · simp [color, hwv, hvu]
  have hcolor : G.Coloring (Option (Option M.edgeSet)) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro a b hab
    have hne : a ≠ b := G.ne_of_adj hab
    intro hEq
    by_cases hau : a = u
    ·
      have hbu : b ≠ u := by
        intro hEq
        exact hne (hau.trans hEq.symm)
      have ha_none : color a = none := by
        simp [color, hau]
      have hb_none : color b = none := hEq.symm.trans ha_none
      exact hbu (color_eq_none_iff.mp hb_none)
    by_cases hav : a = v
    ·
      have hau' : a ≠ u := by
        intro hEq
        exact huv (hEq.symm.trans hav)
      have hbv : b ≠ v := by
        intro hEq
        exact hne (hav.trans hEq.symm)
      have ha_some_none : color a = some none := by
        simp [color, hav, hvu]
      have hb_some_none : color b = some none := hEq.symm.trans ha_some_none
      exact hbv (color_eq_some_none_iff.mp hb_some_none)
    by_cases hbu : b = u
    ·
      have hb_none : color b = none := by
        simp [color, hbu]
      have ha_none : color a = none := hEq.trans hb_none
      exact hau (color_eq_none_iff.mp ha_none)
    by_cases hbv : b = v
    ·
      have hb_some_none : color b = some none := by
        simp [color, hbv, hvu]
      have ha_some_none : color a = some none := hEq.trans hb_some_none
      exact hav (color_eq_some_none_iff.mp ha_some_none)
    have ha_color : color a = some (some (matchedColor a hau hav)) := by
      simp [color, hau, hav]
    have hb_color : color b = some (some (matchedColor b hbu hbv)) := by
      simp [color, hbu, hbv]
    rw [ha_color, hb_color] at hEq
    have hEqColor : matchedColor a hau hav = matchedColor b hbu hbv := by
      exact Option.some.inj (Option.some.inj hEq)
    let a' : Gᶜ.support := supportVertex a hau hav
    let b' : Gᶜ.support := supportVertex b hbu hbv
    rcases
        SimpleGraph.Subgraph.IsMatching.eq_or_adj_of_toEdge_eq hM.1 (hM.2 a') (hM.2 b')
          hEqColor with
      hab_eq | hAdj
    · exact hne (congrArg Subtype.val hab_eq)
    · have hComp : Gᶜ.Adj a b := by
        simpa [H, M, a', b'] using hAdj
      exact ((SimpleGraph.compl_adj G a b).1 hComp).2 hab
  have hsupp : Gᶜ.support = ({u, v} : Set V)ᶜ := by
    ext w
    constructor
    · intro hw
      have hwu : w ≠ u := by
        intro hwu
        exact hu_not_mem (hwu ▸ hw)
      have hwv : w ≠ v := by
        intro hwv
        exact hv_not_mem (hwv ▸ hw)
      simpa [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using
        And.intro hwu hwv
    · intro hw
      have hnot_mem : w ∉ ({u, v} : Set V) := by
        simpa [Set.mem_compl_iff] using hw
      have hwu : w ≠ u := by
        intro hEq
        exact hnot_mem (by simp [hEq])
      have hwv : w ≠ v := by
        intro hEq
        exact hnot_mem (by simp [hEq])
      exact (Gᶜ.degree_pos_iff_mem_support w).1 (by simp [hrest w hwu hwv])
  have hpair : Fintype.card ({u, v} : Set V) = 2 := by
    rw [← Set.toFinset_card]
    simp [huv]
  have hcard_support : Fintype.card Gᶜ.support = 4 := by
    have hcard_support_eq :
        Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v} : Set V) := by
      simpa [hsupp] using (Fintype.card_compl_set ({u, v} : Set V))
    calc
      Fintype.card Gᶜ.support = Fintype.card V - Fintype.card ({u, v} : Set V) := hcard_support_eq
      _ = 6 - 2 := by rw [hcard, hpair]
      _ = 4 := by decide
  have hHdeg : ∀ x : Gᶜ.support, H.degree x = 1 := by
    intro x
    change ((Gᶜ).induce (Gᶜ.support)).degree x = 1
    rw [SimpleGraph.degree_induce_support]
    have hxu : (x : V) ≠ u := by
      intro hxu
      exact hu_not_mem (hxu ▸ x.property)
    have hxv : (x : V) ≠ v := by
      intro hxv
      exact hv_not_mem (hxv ▸ x.property)
    exact hrest x hxu hxv
  have hsum : ∑ x : Gᶜ.support, H.degree x = 4 := by
    calc
      ∑ x : Gᶜ.support, H.degree x = ∑ _ : Gᶜ.support, 1 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hHdeg x
      _ = 4 := by simp [hcard_support]
  have htwice : 2 * H.edgeFinset.card = 4 := by
    rw [← H.sum_degrees_eq_twice_card_edges, hsum]
  have hedge_H : H.edgeFinset.card = 2 := by
    have hdiv := congrArg (fun n : Nat => n / 2) htwice
    simpa using hdiv
  have hcard_colors : Fintype.card M.edgeSet = 2 := by
    simpa [M, SimpleGraph.Subgraph.edgeSet_top] using (H.edgeFinset_card).symm.trans hedge_H
  simpa [Fintype.card_option, hcard_colors] using hcolor.colorable

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph cannot exist.

Source: new theorem combining the exact six-vertex case split with explicit colorings in each
branch. -/
theorem IsIncidenceCriticalNonColorable.not_cliqueFree_six_of_card_eq_six
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    ¬ G.CliqueFree 5 := by
  intro hfree
  rcases h.six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree with h12 | h13
  · exact h.not_colorable
      (h.colorable_four_of_card_eq_six_of_card_edgeFinset_eq_twelve hcard hfree h12.1)
  · exact h.not_colorable
      (h.colorable_four_of_card_eq_six_of_card_edgeFinset_eq_thirteen hcard hfree h13.1)

/-- On six vertices, an incidence-critical non-4-colorable graph contains a `K₅` embedding.

Source: new theorem converting the previous non-`K₅`-free result into embedding form. -/
theorem IsIncidenceCriticalNonColorable.exists_k5_embedding_of_card_eq_six
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) := by
  have hnotfree : ¬ G.CliqueFree 5 := h.not_cliqueFree_six_of_card_eq_six hcard
  exact (SimpleGraph.not_cliqueFree_iff (G := G) 5).1 hnotfree

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a vertex-critical non-4-colorable graph cannot be `K₅`-free.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.not_cliqueFree_six_of_card_eq_six
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    ¬ G.CliqueFree 5 :=
  h.toIncidenceCritical_four.not_cliqueFree_six_of_card_eq_six hcard

/-- On six vertices, a vertex-critical non-4-colorable graph contains a `K₅` embedding.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_k5_embedding_of_card_eq_six
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) :=
  h.toIncidenceCritical_four.exists_k5_embedding_of_card_eq_six hcard

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, an edge-minimal non-4-colorable graph with no isolated vertices cannot be
`K₅`-free.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.not_cliqueFree_six_of_card_eq_six_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) :
    ¬ G.CliqueFree 5 :=
  (h.toIncidenceCritical hadj).not_cliqueFree_six_of_card_eq_six hcard

/-- On six vertices, an edge-minimal non-4-colorable graph with no isolated vertices contains a
`K₅` embedding.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_k5_embedding_of_card_eq_six_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) :=
  (h.toIncidenceCritical hadj).exists_k5_embedding_of_card_eq_six hcard

end MinimalBridge

end FourColor.Curriculum.Actual
