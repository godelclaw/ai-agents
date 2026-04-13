import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointPaths
import FourColor.Curriculum.Actual.SevenVertexFifteenIsolatedColoring
import FourColor.Curriculum.Actual.SevenVertexFifteenEndpointRealization

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the complement of a seven-vertex graph is witnessed by a single path covering all
vertices, then the graph is `4`-colorable.

Source: new theorem closing the connected half of the remaining seven-vertex `15`-edge endpoint
branch by pairing adjacent complement vertices along the spanning path. -/
theorem colorable_four_of_compl_path_covering_all_vertices_of_card_eq_seven
    (hcard : Fintype.card V = 7) {u v : V} {p : Gᶜ.Walk u v}
    (hp : p.IsPath) (hverts : p.toSubgraph.verts = Set.univ) :
    G.Colorable 4 := by
  classical
  have hham : p.IsHamiltonian :=
    hp.isHamiltonian_of_mem (by
      intro x
      rw [← p.mem_verts_toSubgraph, hverts]
      simp)
  have hlen : p.length = 6 := by
    have : p.length = Fintype.card V - 1 := hham.length_eq
    simpa [hcard] using this
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
    apply hmn
    exact hp.getVert_injOn (by rw [Set.mem_setOf_eq]; simpa [hlen] using hm)
      (by rw [Set.mem_setOf_eq]; simpa [hlen] using hn) hEq
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
    have hxsupp : x ∈ p.support := hham.mem_support x
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxsupp with ⟨n, hxn, hn⟩
    have hn6 : n ≤ 6 := by simpa [hlen] using hn
    have hcases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [a0] using hxn.symm)
    · exact Or.inr <| Or.inl (by simpa [a1] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inl (by simpa [a2] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a3] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [a4] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        (by simpa [a5] using hxn.symm)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        (by simpa [a6] using hxn.symm)
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

/-- In the connected half of the remaining seven-vertex `15`-edge endpoint branch, the original
graph is `4`-colorable.

Source: new theorem combining the connected `1,1,2,...,2` complement-path realization with the
explicit four-color partition of the spanning complement path. -/
theorem IsIncidenceCriticalNonColorable.colorable_four_of_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    (hconn : Gᶜ.Connected) :
    G.Colorable 4 := by
  rcases h.fifteen_edge_compl_case_split_reduced_of_card_eq_seven hcard hedge with
    ⟨u, v, huv, hu1, hv1, hrest⟩
  rcases
      exists_path_covering_all_vertices_of_connected_of_distinct_degree_eq_one_and_forall_degree_eq_two_else
        (H := Gᶜ) hconn huv hu1 hv1 hrest with
    ⟨p, hp, hpverts⟩
  exact colorable_four_of_compl_path_covering_all_vertices_of_card_eq_seven
    (G := G) hcard hp hpverts

/-- The connected half of the remaining seven-vertex `15`-edge endpoint branch cannot occur in an
incidence-critical non-4-colorable graph. -/
theorem IsIncidenceCriticalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ¬ Gᶜ.Connected := by
  intro hconn
  exact h.not_colorable
    (h.colorable_four_of_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      hcard hedge hconn)

/-- The seven-vertex `15`-edge endpoint branch reduces to the disconnected path-plus-cycle case.

Source: new theorem eliminating the connected `P7` complement branch from the remaining
seven-vertex `15`-edge frontier. -/
theorem IsIncidenceCriticalNonColorable.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
          ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp := by
  rcases
      h.compl_endpoint_path_and_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
        hcard hedge with
    ⟨u, v, huv, p, hp, hpverts, hsplit⟩
  rcases hsplit with hcov | hdisc
  · exact False.elim <|
      h.not_colorable
        (colorable_four_of_compl_path_covering_all_vertices_of_card_eq_seven
          (G := G) hcard hp (hpverts.trans hcov))
  · exact ⟨u, v, huv, p, hp, hpverts, hdisc⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the connected-branch exclusion in the remaining seven-vertex
`15`-edge endpoint case. -/
theorem IsVertexCriticalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ¬ Gᶜ.Connected :=
  (h.toIncidenceCritical_four).not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

/-- Vertex-critical lift of the reduced seven-vertex `15`-edge endpoint path-plus-cycle split. -/
theorem IsVertexCriticalNonColorable.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
          ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp :=
  (h.toIncidenceCritical_four).compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the connected-branch exclusion in the remaining seven-vertex
`15`-edge endpoint case. -/
theorem IsMinimalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ¬ Gᶜ.Connected :=
  ((h.toIncidenceCritical hadj)).not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

/-- Minimal-counterexample lift of the connected-branch exclusion in the remaining seven-vertex
`15`-edge endpoint case under `K₅`-freeness without a separate no-isolated-vertices
hypothesis. -/
theorem IsMinimalNonColorable.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    ¬ Gᶜ.Connected := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.not_compl_connected_of_card_eq_seven_of_card_edgeFinset_eq_fifteen hcard hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `15`-edge endpoint path-plus-cycle
split. -/
theorem IsMinimalNonColorable.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
          ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp :=
  ((h.toIncidenceCritical hadj)).compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

/-- Minimal-counterexample lift of the reduced seven-vertex `15`-edge endpoint path-plus-cycle
split under `K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    ∃ u v : V, u ≠ v ∧
      ∃ p : (Gᶜ).Walk u v, p.IsPath ∧ p.toSubgraph.verts = ((Gᶜ).connectedComponentMk u).supp ∧
        ∃ d : (Gᶜ).ConnectedComponent, d ≠ (Gᶜ).connectedComponentMk u ∧
          (d.supp.ncard = 3 ∨ d.supp.ncard = 4 ∨ d.supp.ncard = 5) ∧
          ((Gᶜ).connectedComponentMk u).supp ∪ d.supp = Set.univ ∧
          ∃ x : V, ∃ q : (Gᶜ).Walk x x, q.IsCycle ∧ q.toSubgraph.verts = d.supp := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_endpoint_cycle_component_case_split_of_card_eq_seven_of_card_edgeFinset_eq_fifteen hcard hedge

end MinimalBridge

end FourColor.Curriculum.Actual
