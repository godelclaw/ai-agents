import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import FourColor.Curriculum.Actual.CriticalSynthesis

namespace FourColor.Curriculum.Actual

section GenericDensity

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

/-- If every vertex has degree at least `4`, then the handshake identity gives the edge lower bound
`4|V| ≤ 2|E|`.

Source: new theorem combining degree lower bounds with Mathlib's degree-sum identity. -/
theorem four_mul_card_le_two_mul_card_edgeFinset_of_forall_four_le_degree
    (hdeg : ∀ v : V, 4 ≤ G.degree v) :
    4 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  have hsum_le : (∑ _ : V, 4) ≤ ∑ v : V, G.degree v := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact hdeg v
  have hsum_const : (∑ _ : V, 4) = 4 * Fintype.card V := by
    simp [Nat.mul_comm]
  calc
    4 * Fintype.card V = ∑ _ : V, 4 := hsum_const.symm
    _ ≤ ∑ v : V, G.degree v := hsum_le
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- If every vertex has degree at least `4`, then `|E| ≥ 2|V|`.

Source: new theorem derived from `four_mul_card_le_two_mul_card_edgeFinset_of_forall_four_le_degree`
by canceling the common factor `2`. -/
theorem two_mul_card_le_card_edgeFinset_of_forall_four_le_degree
    (hdeg : ∀ v : V, 4 ≤ G.degree v) :
    2 * Fintype.card V ≤ G.edgeFinset.card := by
  have h4 : 4 * Fintype.card V ≤ 2 * G.edgeFinset.card :=
    four_mul_card_le_two_mul_card_edgeFinset_of_forall_four_le_degree (G := G) hdeg
  have h2 : 2 * (2 * Fintype.card V) ≤ 2 * G.edgeFinset.card := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h4
  exact Nat.le_of_mul_le_mul_left h2 Nat.two_pos

/-- A finite simple graph with the maximal possible number of edges is complete.

Source: new theorem using `card_edgeFinset_top_eq_card_choose_two` plus edge-finset extensionality. -/
theorem eq_top_of_card_edgeFinset_eq_card_choose_two
    [DecidableEq V]
    (hcard : G.edgeFinset.card = (Fintype.card V).choose 2) :
    G = (⊤ : SimpleGraph V) := by
  apply (SimpleGraph.edgeFinset_inj).1
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · exact SimpleGraph.edgeFinset_mono (show G ≤ (⊤ : SimpleGraph V) from le_top)
  · exact le_of_eq <| by
      calc
        ((⊤ : SimpleGraph V).edgeFinset.card) = (Fintype.card V).choose 2 := by
          simpa using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V))
        _ = G.edgeFinset.card := hcard.symm

end GenericDensity

section IncidenceCriticalDensity

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Incidence-critical non-4-colorable graphs satisfy `4|V| ≤ 2|E|`.

Source: new specialization of the handshake lower-bound theorem. -/
theorem IsIncidenceCriticalNonColorable.four_mul_card_le_two_mul_card_edgeFinset
    (h : IsIncidenceCriticalNonColorable G 4) :
    4 * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  four_mul_card_le_two_mul_card_edgeFinset_of_forall_four_le_degree
    (G := G) (fun v => h.four_le_degree v)

/-- Incidence-critical non-4-colorable graphs satisfy `|E| ≥ 2|V|`.

Source: new specialization of the handshake lower-bound theorem. -/
theorem IsIncidenceCriticalNonColorable.two_mul_card_le_card_edgeFinset
    (h : IsIncidenceCriticalNonColorable G 4) :
    2 * Fintype.card V ≤ G.edgeFinset.card :=
  two_mul_card_le_card_edgeFinset_of_forall_four_le_degree
    (G := G) (fun v => h.four_le_degree v)

/-- On five vertices, incidence-critical non-4-colorable graphs must have exactly ten edges.

Source: new theorem from the lower bound `|E| ≥ 2|V|` and the universal upper bound
`|E| ≤ choose(|V|, 2)`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_eq_ten_of_card_eq_five
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    G.edgeFinset.card = 10 := by
  have hlow : 2 * Fintype.card V ≤ G.edgeFinset.card := h.two_mul_card_le_card_edgeFinset
  have hlow10 : 10 ≤ G.edgeFinset.card := by
    simpa [hcard] using hlow
  have hupp : G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
  have hupp10 : G.edgeFinset.card ≤ 10 := by
    simpa [hcard] using hupp
  exact Nat.le_antisymm hupp10 hlow10

/-- On five vertices, incidence-critical non-4-colorable graphs are complete.

Source: new theorem from exact edge count at the finite extremal upper bound. -/
theorem IsIncidenceCriticalNonColorable.eq_top_of_card_eq_five
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    G = (⊤ : SimpleGraph V) := by
  have hedge_choose : G.edgeFinset.card = (Fintype.card V).choose 2 := by
    simpa [hcard] using h.card_edgeFinset_eq_ten_of_card_eq_five hcard
  exact eq_top_of_card_edgeFinset_eq_card_choose_two (G := G) hedge_choose

end IncidenceCriticalDensity

section VertexCriticalDensity

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical non-4-colorable graphs satisfy `4|V| ≤ 2|E|`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.four_mul_card_le_two_mul_card_edgeFinset
    (h : IsVertexCriticalNonColorable G 4) :
    4 * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  h.toIncidenceCritical_four.four_mul_card_le_two_mul_card_edgeFinset

/-- Vertex-critical non-4-colorable graphs satisfy `|E| ≥ 2|V|`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.two_mul_card_le_card_edgeFinset
    (h : IsVertexCriticalNonColorable G 4) :
    2 * Fintype.card V ≤ G.edgeFinset.card :=
  h.toIncidenceCritical_four.two_mul_card_le_card_edgeFinset

/-- On five vertices, vertex-critical non-4-colorable graphs must have exactly ten edges.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_eq_ten_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    G.edgeFinset.card = 10 :=
  h.toIncidenceCritical_four.card_edgeFinset_eq_ten_of_card_eq_five hcard

/-- On five vertices, vertex-critical non-4-colorable graphs are complete.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.eq_top_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) :
    G = (⊤ : SimpleGraph V) :=
  h.toIncidenceCritical_four.eq_top_of_card_eq_five hcard

end VertexCriticalDensity

section MinimalDensity

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- For edge-minimal non-4-colorable graphs with no isolated vertices, `4|V| ≤ 2|E|`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.four_mul_card_le_two_mul_card_edgeFinset_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    4 * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).four_mul_card_le_two_mul_card_edgeFinset

/-- For edge-minimal non-4-colorable graphs with no isolated vertices, `|E| ≥ 2|V|`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.two_mul_card_le_card_edgeFinset_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    2 * Fintype.card V ≤ G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).two_mul_card_le_card_edgeFinset

/-- On five vertices, edge-minimal non-4-colorable graphs with no isolated vertices must have
exactly ten edges.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_eq_ten_of_card_eq_five_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 5) :
    G.edgeFinset.card = 10 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_eq_ten_of_card_eq_five hcard

/-- On five vertices, edge-minimal non-4-colorable graphs with no isolated vertices are complete.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.eq_top_of_card_eq_five_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 5) :
    G = (⊤ : SimpleGraph V) :=
  (h.toIncidenceCritical hadj).eq_top_of_card_eq_five hcard

end MinimalDensity

end FourColor.Curriculum.Actual
