import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexRealization

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A cycle whose associated subgraph contains all vertices has length equal to the number of
vertices.

Source: new helper theorem extracting the exact cycle length needed for the connected seven-vertex
branch from a spanning-cycle witness. -/
theorem SimpleGraph.Walk.IsCycle.length_eq_card_of_toSubgraph_verts_eq_univ
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (hverts : p.toSubgraph.verts = Set.univ) :
    p.length = Fintype.card V := by
  let f : Fin p.length → V := fun i => p.getVert i
  have hlen_le : p.length ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective f (by
      intro i j hij
      have hi : (i : ℕ) ≤ p.length - 1 := by omega
      have hj : (j : ℕ) ≤ p.length - 1 := by omega
      apply Fin.ext
      exact hp.getVert_injOn' hi hj hij)
  have hlen_ge : Fintype.card V ≤ p.length := by
    simpa using Fintype.card_le_of_surjective f (by
      intro x
      have hxsupp : x ∈ p.support := by
        rw [← p.mem_verts_toSubgraph, hverts]
        simp
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
      by_cases hnp : n = p.length
      · have h0lt : 0 < p.length := by
          have := hp.three_le_length
          omega
        refine ⟨⟨0, h0lt⟩, ?_⟩
        change p.getVert 0 = x
        calc
          p.getVert 0 = p.getVert p.length := by rw [p.getVert_zero, p.getVert_length]
          _ = x := by simpa [hnp] using hxn
      · have hnlt : n < p.length := by omega
        exact ⟨⟨n, hnlt⟩, by simpa [f] using hxn⟩)
  exact Nat.le_antisymm hlen_le hlen_ge

/-- If the complement of a seven-vertex graph is witnessed by a single cycle covering all
vertices, then the graph is `4`-colorable.

Source: new theorem coloring the original graph by partitioning the spanning complement cycle into
three adjacent pairs and one singleton. -/
theorem colorable_four_of_compl_cycle_covering_all_vertices_of_card_eq_seven
    (hcard : Fintype.card V = 7) {v : V} {p : Gᶜ.Walk v v}
    (hp : p.IsCycle) (hverts : p.toSubgraph.verts = Set.univ) :
    G.Colorable 4 := by
  classical
  have hlen : p.length = 7 := by
    simpa [hcard] using
      (SimpleGraph.Walk.IsCycle.length_eq_card_of_toSubgraph_verts_eq_univ
        (G := Gᶜ) hp hverts)
  let a0 : V := p.getVert 0
  let a1 : V := p.getVert 1
  let a2 : V := p.getVert 2
  let a3 : V := p.getVert 3
  let a4 : V := p.getVert 4
  let a5 : V := p.getVert 5
  let a6 : V := p.getVert 6
  have hget_ne :
      ∀ {m n : ℕ}, m ≤ 6 → n ≤ 6 → m ≠ n → p.getVert m ≠ p.getVert n := by
    intro m n hm hn hmn hEq
    have hm' : m ≤ p.length - 1 := by omega
    have hn' : n ≤ p.length - 1 := by omega
    apply hmn
    exact hp.getVert_injOn' hm' hn' hEq
  have h20 : a2 ≠ a0 := by
    simpa [a2, a0] using hget_ne (m := 2) (n := 0) (by decide) (by decide) (by decide)
  have h21 : a2 ≠ a1 := by
    simpa [a2, a1] using hget_ne (m := 2) (n := 1) (by decide) (by decide) (by decide)
  have h30 : a3 ≠ a0 := by
    simpa [a3, a0] using hget_ne (m := 3) (n := 0) (by decide) (by decide) (by decide)
  have h31 : a3 ≠ a1 := by
    simpa [a3, a1] using hget_ne (m := 3) (n := 1) (by decide) (by decide) (by decide)
  have h40 : a4 ≠ a0 := by
    simpa [a4, a0] using hget_ne (m := 4) (n := 0) (by decide) (by decide) (by decide)
  have h41 : a4 ≠ a1 := by
    simpa [a4, a1] using hget_ne (m := 4) (n := 1) (by decide) (by decide) (by decide)
  have h42 : a4 ≠ a2 := by
    simpa [a4, a2] using hget_ne (m := 4) (n := 2) (by decide) (by decide) (by decide)
  have h43 : a4 ≠ a3 := by
    simpa [a4, a3] using hget_ne (m := 4) (n := 3) (by decide) (by decide) (by decide)
  have h50 : a5 ≠ a0 := by
    simpa [a5, a0] using hget_ne (m := 5) (n := 0) (by decide) (by decide) (by decide)
  have h51 : a5 ≠ a1 := by
    simpa [a5, a1] using hget_ne (m := 5) (n := 1) (by decide) (by decide) (by decide)
  have h52 : a5 ≠ a2 := by
    simpa [a5, a2] using hget_ne (m := 5) (n := 2) (by decide) (by decide) (by decide)
  have h53 : a5 ≠ a3 := by
    simpa [a5, a3] using hget_ne (m := 5) (n := 3) (by decide) (by decide) (by decide)
  have h60 : a6 ≠ a0 := by
    simpa [a6, a0] using hget_ne (m := 6) (n := 0) (by decide) (by decide) (by decide)
  have h61 : a6 ≠ a1 := by
    simpa [a6, a1] using hget_ne (m := 6) (n := 1) (by decide) (by decide) (by decide)
  have h62 : a6 ≠ a2 := by
    simpa [a6, a2] using hget_ne (m := 6) (n := 2) (by decide) (by decide) (by decide)
  have h63 : a6 ≠ a3 := by
    simpa [a6, a3] using hget_ne (m := 6) (n := 3) (by decide) (by decide) (by decide)
  have h64 : a6 ≠ a4 := by
    simpa [a6, a4] using hget_ne (m := 6) (n := 4) (by decide) (by decide) (by decide)
  have h65 : a6 ≠ a5 := by
    simpa [a6, a5] using hget_ne (m := 6) (n := 5) (by decide) (by decide) (by decide)
  have h01adj : Gᶜ.Adj a0 a1 := by
    have h0 : 0 < p.length := by omega
    simpa [a0, a1] using p.adj_getVert_succ h0
  have h23adj : Gᶜ.Adj a2 a3 := by
    have h2 : 2 < p.length := by omega
    simpa [a2, a3] using p.adj_getVert_succ h2
  have h45adj : Gᶜ.Adj a4 a5 := by
    have h4 : 4 < p.length := by omega
    simpa [a4, a5] using p.adj_getVert_succ h4
  have hcover :
      ∀ x : V, x = a0 ∨ x = a1 ∨ x = a2 ∨ x = a3 ∨ x = a4 ∨ x = a5 ∨ x = a6 := by
    intro x
    have hxsupp : x ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hverts]
      simp
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn7 : n ≤ 7 := by simpa [hlen] using hn
    have hcases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [a0] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [a2] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a3] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a4] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a5] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (by simpa [a6] using hxn.symm)
    · exact Or.inl <| by
        calc
          x = p.getVert 7 := hxn.symm
          _ = p.getVert p.length := by simpa [hlen]
          _ = p.getVert 0 := by rw [p.getVert_length, p.getVert_zero]
          _ = a0 := rfl
  let color : V → Fin 4 := fun x =>
    if x = a0 ∨ x = a1 then 0
    else if x = a2 ∨ x = a3 then 1
    else if x = a4 ∨ x = a5 then 2
    else 3
  have hcolor_a0 : color a0 = 0 := by
    simp [color]
  have hcolor_a1 : color a1 = 0 := by
    simp [color]
  have hcolor_a2 : color a2 = 1 := by
    simp [color, h20, h21]
  have hcolor_a3 : color a3 = 1 := by
    simp [color, h30, h31]
  have hcolor_a4 : color a4 = 2 := by
    simp [color, h40, h41, h42, h43]
  have hcolor_a5 : color a5 = 2 := by
    simp [color, h50, h51, h52, h53]
  have hcolor_a6 : color a6 = 3 := by
    simp [color, h60, h61, h62, h63, h64, h65]
  have bucket0 {x : V} (hx : color x = 0) : x = a0 ∨ x = a1 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a2] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a4] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a5] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a6] using hx
      exact False.elim this
  have bucket1 {x : V} (hx : color x = 1) : x = a2 ∨ x = a3 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a4] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a5] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a6] using hx
      exact False.elim this
  have bucket2 {x : V} (hx : color x = 2) : x = a4 ∨ x = a5 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : False := by simpa [hcolor_a0] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a1] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a2] using hx
      exact False.elim this
    · have : False := by simpa [hcolor_a3] using hx
      exact False.elim this
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have : False := by simpa [hcolor_a6] using hx
      exact False.elim this
  have bucket3 {x : V} (hx : color x = 3) : x = a6 := by
    rcases hcover x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [hcolor_a0] using hx
    · simpa [hcolor_a1] using hx
    · simpa [hcolor_a2] using hx
    · simpa [hcolor_a3] using hx
    · simpa [hcolor_a4] using hx
    · simpa [hcolor_a5] using hx
    · rfl
  have hcolor : G.Coloring (Fin 4) := by
    refine SimpleGraph.Coloring.mk color ?_
    intro x y hxy
    intro hEq
    by_cases hx01 : x = a0 ∨ x = a1
    · have hcx : color x = 0 := by simp [color, hx01]
      have hcy : color y = 0 := by rw [← hEq, hcx]
      rcases hx01 with rfl | rfl
      · rcases bucket0 hcy with rfl | rfl
        · exact (G.ne_of_adj hxy) rfl
        · exact ((SimpleGraph.compl_adj G a0 a1).1 h01adj).2 hxy
      · rcases bucket0 hcy with rfl | rfl
        · exact ((SimpleGraph.compl_adj G a1 a0).1 h01adj.symm).2 hxy
        · exact (G.ne_of_adj hxy) rfl
    · by_cases hx23 : x = a2 ∨ x = a3
      · have hcx : color x = 1 := by simp [color, hx01, hx23]
        have hcy : color y = 1 := by rw [← hEq, hcx]
        rcases hx23 with rfl | rfl
        · rcases bucket1 hcy with rfl | rfl
          · exact (G.ne_of_adj hxy) rfl
          · exact ((SimpleGraph.compl_adj G a2 a3).1 h23adj).2 hxy
        · rcases bucket1 hcy with rfl | rfl
          · exact ((SimpleGraph.compl_adj G a3 a2).1 h23adj.symm).2 hxy
          · exact (G.ne_of_adj hxy) rfl
      · by_cases hx45 : x = a4 ∨ x = a5
        · have hcx : color x = 2 := by simp [color, hx01, hx23, hx45]
          have hcy : color y = 2 := by rw [← hEq, hcx]
          rcases hx45 with rfl | rfl
          · rcases bucket2 hcy with rfl | rfl
            · exact (G.ne_of_adj hxy) rfl
            · exact ((SimpleGraph.compl_adj G a4 a5).1 h45adj).2 hxy
          · rcases bucket2 hcy with rfl | rfl
            · exact ((SimpleGraph.compl_adj G a5 a4).1 h45adj.symm).2 hxy
            · exact (G.ne_of_adj hxy) rfl
        · have hcx : color x = 3 := by simp [color, hx01, hx23, hx45]
          have hcy : color y = 3 := by rw [← hEq, hcx]
          rw [bucket3 hcx, bucket3 hcy] at hxy
          exact G.loopless a6 hxy
  exact hcolor.colorable

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the connected branch of the sharp seven-vertex low-edge case, the original graph is
`4`-colorable.

Source: new theorem combining the complement spanning-cycle realization with an explicit four-color
partition of the seven-cycle. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14)
    (hconn : Gᶜ.Connected) :
    G.Colorable 4 := by
  rcases h.compl_exists_cycle_covering_all_vertices_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
      hcard hedge hconn with ⟨v, p, hp, hpverts⟩
  exact colorable_four_of_compl_cycle_covering_all_vertices_of_card_eq_seven
    (G := G) hcard hp hpverts

/-- The connected branch of the sharp seven-vertex low-edge case cannot occur in an
incidence-critical non-4-colorable graph.

Source: new theorem using the previous explicit coloring result to eliminate the connected
seven-vertex complement branch. -/
theorem IsIncidenceCriticalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ¬ Gᶜ.Connected := by
  intro hconn
  exact h.not_colorable
    (h.colorable_four_of_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
      hcard hedge hconn)

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the connected-branch exclusion in the sharp seven-vertex low-edge
case. -/
theorem IsVertexCriticalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ¬ Gᶜ.Connected :=
  (h.toIncidenceCritical_four).not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the connected-branch exclusion in the sharp seven-vertex
low-edge case. -/
theorem IsMinimalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ¬ Gᶜ.Connected :=
  ((h.toIncidenceCritical hadj)).not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- Minimal-counterexample lift of the connected-branch exclusion in the sharp seven-vertex
low-edge case under `K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    ¬ Gᶜ.Connected := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
