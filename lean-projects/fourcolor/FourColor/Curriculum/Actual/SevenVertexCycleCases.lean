import FourColor.Curriculum.Actual.SevenVertexCycles

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every connected component of a finite `2`-regular graph has at least three vertices.

Source: new helper theorem for the seven-vertex branch, obtained by choosing a vertex in the
component and using its two distinct neighbors. -/
theorem connectedComponent_ncard_ge_three_of_isRegularOfDegree_two
    (hreg : G.IsRegularOfDegree 2) (c : G.ConnectedComponent) :
    3 ≤ c.supp.ncard := by
  let v : V := c.nonempty_supp.some
  have hv : v ∈ c.supp := c.nonempty_supp.some_mem
  have htwo : (G.neighborSet v).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree, hreg v]
  obtain ⟨w₁, w₂, hw12, hset⟩ := Set.ncard_eq_two.mp htwo
  have hw₁mem : w₁ ∈ G.neighborSet v := by rw [hset]; simp
  have hw₂mem : w₂ ∈ G.neighborSet v := by rw [hset]; simp
  have hw₁adj : G.Adj v w₁ := by simpa [SimpleGraph.mem_neighborSet] using hw₁mem
  have hw₂adj : G.Adj v w₂ := by simpa [SimpleGraph.mem_neighborSet] using hw₂mem
  have hw₁ : w₁ ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hw₁adj
  have hw₂ : w₂ ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hw₂adj
  have hvw₁ : v ≠ w₁ := G.ne_of_adj hw₁adj
  have hvw₂ : v ≠ w₂ := G.ne_of_adj hw₂adj
  have hgt : 2 < c.supp.ncard := by
    exact (Set.two_lt_ncard).2 ⟨v, hv, w₁, hw₁, w₂, hw₂, hvw₁, hvw₂, hw12⟩
  exact Nat.succ_le_of_lt hgt

/-- If a connected component of a finite graph occupies all vertices, the graph is connected.

Source: new helper theorem for converting the `7`-vertex component case into the connected branch
of the seven-vertex `2`-regular classification. -/
theorem connected_of_connectedComponent_ncard_eq_card
    (c : G.ConnectedComponent) (hc : c.supp.ncard = Fintype.card V) :
    G.Connected := by
  have hsupp : c.supp = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (show c.supp ⊆ Set.univ by intro x hx; simp)
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using hc.ge
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨c.nonempty_supp.some, ?_⟩
  intro w
  have hv : c.nonempty_supp.some ∈ c.supp := c.nonempty_supp.some_mem
  have hw : w ∈ c.supp := by simp [hsupp]
  exact c.reachable_of_mem_supp hv hw

/-- A finite `2`-regular graph on seven vertices has a connected component of size `3` or `7`.

Source: new theorem combining odd-component parity, the lower bound `|C| ≥ 3` on every component,
and exclusion of the impossible `|C| = 5` case. -/
theorem exists_component_card_three_or_seven_of_card_eq_seven_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 7) (hreg : G.IsRegularOfDegree 2) :
    ∃ c : G.ConnectedComponent, c.supp.ncard = 3 ∨ c.supp.ncard = 7 := by
  have hoddV : Odd (Nat.card V) := by
    simpa [Nat.card_eq_fintype_card, hcard] using (show Odd 7 by decide)
  have hoddComps : Odd G.oddComponents.ncard := by
    exact (SimpleGraph.odd_ncard_oddComponents (G := G)).2 hoddV
  have hnonempty : G.oddComponents.Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hoddComps.pos)
  rcases hnonempty with ⟨c, hcodd⟩
  have hge3 : 3 ≤ c.supp.ncard :=
    connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg c
  have hle7 : c.supp.ncard ≤ 7 := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (Set.ncard_le_ncard (show c.supp ⊆ Set.univ by intro x hx; simp))
  have hne5 : c.supp.ncard ≠ 5 := by
    intro hc5
    have hlt : c.supp.ncard < (Set.univ : Set V).ncard := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hc5]
      decide
    obtain ⟨v, -, hvnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    let d : G.ConnectedComponent := G.connectedComponentMk v
    have hvd : v ∈ d.supp := by
      simpa [d] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G) (v := v))
    have hdc : d ≠ c := by
      intro hdc
      exact hvnot (hdc ▸ hvd)
    have hdisj : Disjoint d.supp c.supp :=
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent (G := G)) hdc
    have hdsubset : d.supp ⊆ Set.univ \ c.supp := by
      intro x hx
      refine ⟨by simp, ?_⟩
      exact Set.disjoint_left.mp hdisj hx
    have hdle2 : d.supp.ncard ≤ 2 := by
      calc
        d.supp.ncard ≤ (Set.univ \ c.supp).ncard := Set.ncard_le_ncard hdsubset
        _ = 2 := by
          rw [Set.ncard_diff (show c.supp ⊆ (Set.univ : Set V) by intro x hx; simp)]
          simp [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hc5]
    have hdge3 : 3 ≤ d.supp.ncard :=
      connectedComponent_ncard_ge_three_of_isRegularOfDegree_two hreg d
    exact (show ¬ 3 ≤ 2 by decide) (hdge3.trans hdle2)
  have hcases : c.supp.ncard = 3 ∨ c.supp.ncard = 7 := by
    have hrange :
        c.supp.ncard = 3 ∨ c.supp.ncard = 4 ∨ c.supp.ncard = 5 ∨
          c.supp.ncard = 6 ∨ c.supp.ncard = 7 := by
      omega
    rcases hrange with hc3 | hc4 | hc5 | hc6 | hc7
    · exact Or.inl hc3
    · exfalso
      have hodd : Odd c.supp.ncard := by simpa [SimpleGraph.oddComponents] using hcodd
      rw [hc4] at hodd
      exact (by decide : ¬ Odd 4) hodd
    · exfalso
      exact hne5 hc5
    · exfalso
      have hodd : Odd c.supp.ncard := by simpa [SimpleGraph.oddComponents] using hcodd
      rw [hc6] at hodd
      exact (by decide : ¬ Odd 6) hodd
    · exact Or.inr hc7
  exact ⟨c, hcases⟩

/-- A finite `2`-regular graph on seven vertices is either connected or has a `3`-vertex
connected component.

Source: new theorem packaging the previous size split into the exact case distinction needed for
the seven-vertex complement branch. -/
theorem connected_or_exists_component_card_three_of_card_eq_seven_of_isRegularOfDegree_two
    (hcard : Fintype.card V = 7) (hreg : G.IsRegularOfDegree 2) :
    G.Connected ∨ ∃ c : G.ConnectedComponent, c.supp.ncard = 3 := by
  rcases exists_component_card_three_or_seven_of_card_eq_seven_of_isRegularOfDegree_two
      (G := G) hcard hreg with ⟨c, hc | hc⟩
  · exact Or.inr ⟨c, hc⟩
  · exact Or.inl (connected_of_connectedComponent_ncard_eq_card (G := G) c (by simpa [hcard] using hc))

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the sharp seven-vertex low-edge branch, the complement is either connected or has a
`3`-vertex connected component.

Source: new theorem specializing the generic seven-vertex `2`-regular classification to the
complement of an incidence-critical non-4-colorable graph. -/
theorem IsIncidenceCriticalNonColorable.compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.Connected ∨ ∃ c : (Gᶜ).ConnectedComponent, c.supp.ncard = 3 := by
  exact connected_or_exists_component_card_three_of_card_eq_seven_of_isRegularOfDegree_two
    (G := Gᶜ) hcard
    (h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge)

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the sharp seven-vertex complement case split. -/
theorem IsVertexCriticalNonColorable.compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.Connected ∨ ∃ c : (Gᶜ).ConnectedComponent, c.supp.ncard = 3 := by
  exact (h.toIncidenceCritical_four).compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the sharp seven-vertex complement case split. -/
theorem IsMinimalNonColorable.compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.Connected ∨ ∃ c : (Gᶜ).ConnectedComponent, c.supp.ncard = 3 := by
  exact ((h.toIncidenceCritical hadj)).compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

/-- Minimal-counterexample lift of the sharp seven-vertex complement case split under `K₅`-freeness
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.Connected ∨ ∃ c : (Gᶜ).ConnectedComponent, c.supp.ncard = 3 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_connected_or_exists_component_card_three_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

end MinimalBranch

end FourColor.Curriculum.Actual
