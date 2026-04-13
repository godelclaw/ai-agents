import Mathlib.Combinatorics.SimpleGraph.Circulant
import FourColor.Curriculum.Actual.SevenVertexSixteenIsolatedSupport
import FourColor.Curriculum.Actual.SevenVertexDisconnectedColoring

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A finite `2`-regular graph on five vertices is exactly a transported copy of `cycleGraph 5`.

Source: this packages the existing five-vertex connected-cycle realization into a canonical graph
equality, not just a spanning cycle witness. The proof indexes the spanning cycle by `Fin 5`,
shows those indexed vertices are bijective, and then identifies the graph by exact neighbor sets.
-/
theorem exists_equiv_cycleGraph_five_of_card_eq_five_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 5) (hreg : G.IsRegularOfDegree 2) :
    ∃ e : Fin 5 ≃ V, G = (SimpleGraph.cycleGraph 5).map e.toEmbedding := by
  classical
  rcases exists_cycle_covering_all_vertices_of_card_eq_five_of_isRegularOfDegree_two
      (G := G) hcard hreg with ⟨x, p, hpc, hpverts⟩
  have hlen : p.length = 5 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (SimpleGraph.Walk.IsCycle.length_eq_ncard_of_toSubgraph_verts_eq (G := G) hpc hpverts)
  let f : Fin 5 → V := fun i => p.getVert i
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hi : (i : ℕ) ≤ p.length - 1 := by omega
    have hj : (j : ℕ) ≤ p.length - 1 := by omega
    exact hpc.getVert_injOn' hi hj hij
  have hf_surj : Function.Surjective f := by
    intro y
    have hyverts : y ∈ p.toSubgraph.verts := by
      rw [hpverts]
      simp
    have hysupp : y ∈ p.support := p.mem_verts_toSubgraph.mp hyverts
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hysupp with ⟨n, hyn, hnle⟩
    by_cases hn : n = p.length
    · refine ⟨0, ?_⟩
      calc
        f 0 = p.getVert 0 := rfl
        _ = p.getVert p.length := by rw [p.getVert_zero, p.getVert_length]
        _ = y := by simpa [hn] using hyn
    · have hnlt : n < p.length := by omega
      refine ⟨⟨n, by simpa [hlen] using hnlt⟩, ?_⟩
      simpa [f] using hyn
  let e : Fin 5 ≃ V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hneigh_two : ∀ y : V, (G.neighborSet y).ncard = 2 := by
    intro y
    have hcard' : Fintype.card ↥(G.neighborSet y) = 2 := by
      simpa [hreg y] using (G.card_neighborSet_eq_degree (v := y))
    have hcard_eq : Fintype.card ↥(G.neighborSet y) = (G.neighborSet y).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hcard_eq] using hcard'
  have hsnd : p.snd = f 1 := by
    simp [f]
  have hpen : p.penultimate = f 4 := by
    change p.penultimate = p.getVert 4
    simpa [SimpleGraph.Walk.penultimate, hlen]
  have hget5 : p.getVert 5 = f 0 := by
    calc
      p.getVert 5 = p.getVert p.length := by simp [hlen]
      _ = p.getVert 0 := by rw [p.getVert_length, p.getVert_zero]
      _ = f 0 := rfl
  have h01 : f 0 ≠ f 1 := by
    exact fun hEq => by
      have : (0 : ℕ) = 1 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h02 : f 0 ≠ f 2 := by
    exact fun hEq => by
      have : (0 : ℕ) = 2 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h03 : f 0 ≠ f 3 := by
    exact fun hEq => by
      have : (0 : ℕ) = 3 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h04 : f 0 ≠ f 4 := by
    exact fun hEq => by
      have : (0 : ℕ) = 4 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h12 : f 1 ≠ f 2 := by
    exact fun hEq => by
      have : (1 : ℕ) = 2 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h13 : f 1 ≠ f 3 := by
    exact fun hEq => by
      have : (1 : ℕ) = 3 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h14 : f 1 ≠ f 4 := by
    exact fun hEq => by
      have : (1 : ℕ) = 4 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h23 : f 2 ≠ f 3 := by
    exact fun hEq => by
      have : (2 : ℕ) = 3 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h24 : f 2 ≠ f 4 := by
    exact fun hEq => by
      have : (2 : ℕ) = 4 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have h34 : f 3 ≠ f 4 := by
    exact fun hEq => by
      have : (3 : ℕ) = 4 := hpc.getVert_injOn' (by simpa [hlen]) (by simpa [hlen]) hEq
      omega
  have hneigh0_sub : p.toSubgraph.neighborSet (f 0) = {f 1, f 4} := by
    have h0 :=
      (hpc.neighborSet_toSubgraph_endpoint :
        p.toSubgraph.neighborSet x = {p.snd, p.penultimate})
    rw [hsnd, hpen] at h0
    simpa [f, p.getVert_zero] using h0
  have hneigh1_sub : p.toSubgraph.neighborSet (f 1) = {f 0, f 2} := by
    simpa [f] using hpc.neighborSet_toSubgraph_internal (i := 1) (by decide) (by omega)
  have hneigh2_sub : p.toSubgraph.neighborSet (f 2) = {f 1, f 3} := by
    simpa [f] using hpc.neighborSet_toSubgraph_internal (i := 2) (by decide) (by omega)
  have hneigh3_sub : p.toSubgraph.neighborSet (f 3) = {f 2, f 4} := by
    simpa [f] using hpc.neighborSet_toSubgraph_internal (i := 3) (by decide) (by omega)
  have hneigh4_sub : p.toSubgraph.neighborSet (f 4) = {f 3, f 0} := by
    simpa [f, hget5] using hpc.neighborSet_toSubgraph_internal (i := 4) (by decide) (by omega)
  have hneigh0 : G.neighborSet (f 0) = {f 1, f 4} := by
    have hEq : p.toSubgraph.neighborSet (f 0) = G.neighborSet (f 0) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (f 0)) (by
        rw [hneigh0_sub, hneigh_two (f 0)]
        simp [h14])
    exact hEq.symm.trans hneigh0_sub
  have hneigh1 : G.neighborSet (f 1) = {f 0, f 2} := by
    have hEq : p.toSubgraph.neighborSet (f 1) = G.neighborSet (f 1) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (f 1)) (by
        rw [hneigh1_sub, hneigh_two (f 1)]
        simp [h02])
    exact hEq.symm.trans hneigh1_sub
  have hneigh2 : G.neighborSet (f 2) = {f 1, f 3} := by
    have hEq : p.toSubgraph.neighborSet (f 2) = G.neighborSet (f 2) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (f 2)) (by
        rw [hneigh2_sub, hneigh_two (f 2)]
        simp [h13])
    exact hEq.symm.trans hneigh2_sub
  have hneigh3 : G.neighborSet (f 3) = {f 2, f 4} := by
    have hEq : p.toSubgraph.neighborSet (f 3) = G.neighborSet (f 3) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (f 3)) (by
        rw [hneigh3_sub, hneigh_two (f 3)]
        simp [h24])
    exact hEq.symm.trans hneigh3_sub
  have hneigh4 : G.neighborSet (f 4) = {f 3, f 0} := by
    have hEq : p.toSubgraph.neighborSet (f 4) = G.neighborSet (f 4) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (f 4)) (by
        rw [hneigh4_sub, hneigh_two (f 4)]
        rw [Set.ncard_pair h03.symm])
    exact hEq.symm.trans hneigh4_sub
  have hneigh_e : ∀ i : Fin 5, G.neighborSet (e i) = {e (i - 1), e (i + 1)} := by
    intro i
    fin_cases i
    · simpa [e, f, Set.pair_comm] using hneigh0
    · simpa [e, f] using hneigh1
    · simpa [e, f] using hneigh2
    · simpa [e, f] using hneigh3
    · simpa [e, f] using hneigh4
  have hadj_e : ∀ i j : Fin 5, G.Adj (e i) (e j) ↔ (SimpleGraph.cycleGraph 5).Adj i j := by
    intro i j
    rw [← SimpleGraph.mem_neighborSet, hneigh_e i, ← SimpleGraph.mem_neighborSet,
      SimpleGraph.cycleGraph_neighborSet]
    constructor
    · intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (e.injective h)
      · exact Or.inr (e.injective h)
    · intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (by simpa [h])
      · exact Or.inr (by simpa [h])
  use e
  ext u v
  rcases e.surjective u with ⟨i, rfl⟩
  rcases e.surjective v with ⟨j, rfl⟩
  simpa [SimpleGraph.map_adj_apply] using hadj_e i j

/-- Isomorphism version of the five-vertex connected `2`-regular classification. -/
theorem nonempty_iso_cycleGraph_five_of_card_eq_five_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 5) (hreg : G.IsRegularOfDegree 2) :
    Nonempty (SimpleGraph.cycleGraph 5 ≃g G) := by
  rcases exists_equiv_cycleGraph_five_of_card_eq_five_of_isRegularOfDegree_two
      (G := G) hcard hreg with ⟨e, hEq⟩
  subst hEq
  exact ⟨SimpleGraph.Iso.map e (SimpleGraph.cycleGraph 5)⟩

end Generic

end FourColor.Curriculum.Actual
