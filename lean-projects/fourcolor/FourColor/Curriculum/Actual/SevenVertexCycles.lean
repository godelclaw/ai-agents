import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import FourColor.Curriculum.Actual.SevenVertexStructure

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A finite `2`-regular graph is a graph of cycles in Mathlib's sense.

Source: helper theorem packaging the finite-neighbor-set cardinality computation needed for the
seven-vertex complement branch. -/
theorem isCycles_of_isRegularOfDegree_two
    (h : G.IsRegularOfDegree 2) : G.IsCycles := by
  intro v hv
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree, h v]

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, the complement always has an odd connected component.

Source: new theorem from the odd-component parity identity on finite graphs and the fact that seven
is odd. -/
theorem compl_exists_odd_component_of_card_eq_seven_generic
    (G : SimpleGraph V) (hcard : Fintype.card V = 7) :
    ∃ c : (Gᶜ).ConnectedComponent, Odd c.supp.ncard := by
  have hoddV : Odd (Nat.card V) := by
    simpa [Nat.card_eq_fintype_card, hcard] using (show Odd 7 by decide)
  have hoddComps : Odd (Gᶜ).oddComponents.ncard := by
    exact (SimpleGraph.odd_ncard_oddComponents (G := Gᶜ)).2 hoddV
  have hnonempty : (Gᶜ).oddComponents.Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hoddComps.pos)
  rcases hnonempty with ⟨c, hc⟩
  exact ⟨c, hc⟩

/-- In the sharp seven-vertex low-edge branch, the complement is a graph of cycles.

Source: new theorem from the previously proved `2`-regularity of the complement. -/
theorem IsIncidenceCriticalNonColorable.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsCycles := by
  exact isCycles_of_isRegularOfDegree_two
    (h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge)

/-- In the sharp seven-vertex low-edge branch, the complement has an odd connected component.

Source: new theorem specialized from the generic seven-vertex complement parity lemma. -/
theorem IsIncidenceCriticalNonColorable.compl_exists_odd_component_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ∃ c : (Gᶜ).ConnectedComponent, Odd c.supp.ncard := by
  exact compl_exists_odd_component_of_card_eq_seven_generic G hcard

/-- In the sharp seven-vertex low-edge branch, the complement contains an odd cycle whose support
is exactly one connected component.

Source: new theorem combining complement `IsCycles`, odd-component existence, and Mathlib's cycle
extraction theorem for connected components of cycle graphs. -/
theorem IsIncidenceCriticalNonColorable.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ∃ (v : V) (p : (Gᶜ).Walk v v), p.IsCycle ∧ Odd p.toSubgraph.verts.ncard := by
  have hcyc : Gᶜ.IsCycles :=
    h.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge
  rcases IsIncidenceCriticalNonColorable.compl_exists_odd_component_of_card_eq_seven
      (G := G) hcard with
    ⟨c, hcodd⟩
  let v : V := c.nonempty_supp.some
  have hv : v ∈ c.supp := c.nonempty_supp.some_mem
  have hreg : Gᶜ.IsRegularOfDegree 2 :=
    h.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge
  have hdeg : (Gᶜ).degree v = 2 := hreg v
  have hdeg_pos : 0 < (Gᶜ).degree v := by simp [hdeg]
  have hneigh : ((Gᶜ).neighborSet v).Nonempty := by
    rcases ((Gᶜ).degree_pos_iff_exists_adj v).1 hdeg_pos with ⟨w, hw⟩
    exact ⟨w, hw⟩
  rcases hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := c) hv hneigh with
    ⟨p, hpcycle, hpverts⟩
  have hpodd : Odd p.toSubgraph.verts.ncard := by
    rw [hpverts]
    exact hcodd
  refine ⟨v, p, hpcycle, ?_⟩
  simpa using hpodd

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex complement cycle-structure theorem. -/
theorem IsVertexCriticalNonColorable.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsCycles :=
  h.toIncidenceCritical_four.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- Vertex-critical lift of the seven-vertex odd-cycle extraction theorem. -/
theorem IsVertexCriticalNonColorable.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ∃ (v : V) (p : (Gᶜ).Walk v v), p.IsCycle ∧ Odd p.toSubgraph.verts.ncard :=
  h.toIncidenceCritical_four.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex complement cycle-structure theorem. -/
theorem IsMinimalNonColorable.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsCycles :=
  (h.toIncidenceCritical hadj).compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- Minimal-counterexample lift of the seven-vertex complement cycle-structure theorem under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsCycles := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_isCycles_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

/-- Minimal-counterexample lift of the seven-vertex odd-cycle extraction theorem. -/
theorem IsMinimalNonColorable.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    ∃ (v : V) (p : (Gᶜ).Walk v v), p.IsCycle ∧ Odd p.toSubgraph.verts.ncard :=
  (h.toIncidenceCritical hadj).compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- Minimal-counterexample lift of the seven-vertex odd-cycle extraction theorem under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    ∃ (v : V) (p : (Gᶜ).Walk v v), p.IsCycle ∧ Odd p.toSubgraph.verts.ncard := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_exists_odd_cycle_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

end MinimalBranch

end FourColor.Curriculum.Actual
