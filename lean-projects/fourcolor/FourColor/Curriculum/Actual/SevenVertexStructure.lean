import Mathlib.Combinatorics.SimpleGraph.Finite
import FourColor.Curriculum.Actual.SevenVertexBounds
import FourColor.Curriculum.Actual.SupportReduction

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, edge count `14` in an incidence-critical non-4-colorable graph forces every
vertex to have degree `4`.

Source: new theorem from the lower bound `degree ≥ 4` at every vertex plus handshaking:
`2|E| = 28` leaves no room for any degree strictly above `4`. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) (v : V) :
    G.degree v = 4 := by
  have hge4 : 4 ≤ G.degree v := h.four_le_degree v
  by_contra hne4
  have hge5 : 5 ≤ G.degree v := by
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hge4 (by simpa [eq_comm] using hne4))
  have hcard_erase : (Finset.univ.erase v).card = 6 := by
    have hv_mem : v ∈ Finset.univ := by simp
    rw [Finset.card_erase_of_mem hv_mem, Finset.card_univ, hcard]
  have hsum_erase_ge24 :
      24 ≤ Finset.sum (Finset.univ.erase v) (fun w => G.degree w) := by
    calc
      24 = 4 * (Finset.univ.erase v).card := by rw [hcard_erase]
      _ = Finset.sum (Finset.univ.erase v) (fun _ => 4) := by simp [Nat.mul_comm]
      _ ≤ Finset.sum (Finset.univ.erase v) (fun w => G.degree w) := by
        refine Finset.sum_le_sum ?_
        intro w hw
        exact h.four_le_degree w
  have hsum_ge29 : 29 ≤ Finset.sum Finset.univ (fun w => G.degree w) := by
    have hsplit :
        G.degree v + Finset.sum (Finset.univ.erase v) (fun w => G.degree w) =
          Finset.sum Finset.univ (fun w => G.degree w) := by
      simpa using
        (Finset.add_sum_erase (s := Finset.univ) (f := fun w => G.degree w) (by simp : v ∈ Finset.univ))
    calc
      29 = 5 + 24 := by decide
      _ ≤ G.degree v + Finset.sum (Finset.univ.erase v) (fun w => G.degree w) := by
        exact Nat.add_le_add hge5 hsum_erase_ge24
      _ = Finset.sum Finset.univ (fun w => G.degree w) := hsplit
  have hsum_eq28 : Finset.sum Finset.univ (fun w => G.degree w) = 28 := by
    calc
      Finset.sum Finset.univ (fun w => G.degree w) = ∑ w : V, G.degree w := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 28 := by rw [hedge]
  have : 29 ≤ 28 := by
    have htmp : 29 ≤ Finset.sum Finset.univ (fun w => G.degree w) := hsum_ge29
    rwa [hsum_eq28] at htmp
  exact (by decide : ¬ (29 ≤ 28)) this

/-- On seven vertices, edge count `14` in an incidence-critical non-4-colorable graph forces
`4`-regularity.

Source: new theorem packaging the previous pointwise degree computation. -/
theorem IsIncidenceCriticalNonColorable.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    G.IsRegularOfDegree 4 := by
  intro v
  exact h.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge v

/-- On seven vertices, edge count `14` in an incidence-critical non-4-colorable graph forces the
complement to be `2`-regular.

Source: new theorem from exact `4`-regularity of the graph plus Mathlib's complement-regularity
formula. -/
theorem IsIncidenceCriticalNonColorable.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsRegularOfDegree 2 := by
  have hreg : G.IsRegularOfDegree 4 :=
    h.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge
  simpa [hcard] using (SimpleGraph.IsRegularOfDegree.compl (G := G) (k := 4) hreg)

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, edge count `14` in a vertex-critical non-4-colorable graph forces every
vertex to have degree `4`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) (v : V) :
    G.degree v = 4 :=
  h.toIncidenceCritical_four.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge v

/-- On seven vertices, edge count `14` in a vertex-critical non-4-colorable graph forces
`4`-regularity.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    G.IsRegularOfDegree 4 :=
  h.toIncidenceCritical_four.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- On seven vertices, edge count `14` in a vertex-critical non-4-colorable graph forces the
complement to be `2`-regular.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsRegularOfDegree 2 :=
  h.toIncidenceCritical_four.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, edge count `14` in an edge-minimal non-4-colorable graph with no isolated
vertices forces every vertex to have degree `4`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) (v : V) :
    G.degree v = 4 :=
  (h.toIncidenceCritical hadj).degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge v

/-- On seven vertices, edge count `14` in a `K₅`-free edge-minimal non-4-colorable graph forces
every vertex to have degree `4` without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) (v : V) :
    G.degree v = 4 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge v

/-- On seven vertices, edge count `14` in an edge-minimal non-4-colorable graph with no isolated
vertices forces `4`-regularity.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    G.IsRegularOfDegree 4 :=
  (h.toIncidenceCritical hadj).isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- On seven vertices, edge count `14` in a `K₅`-free edge-minimal non-4-colorable graph forces
`4`-regularity without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    G.IsRegularOfDegree 4 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.isRegularOfDegree_four_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

/-- On seven vertices, edge count `14` in an edge-minimal non-4-colorable graph with no isolated
vertices forces the complement to be `2`-regular.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsRegularOfDegree 2 :=
  (h.toIncidenceCritical hadj).compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen
    hcard hedge

/-- On seven vertices, edge count `14` in a `K₅`-free edge-minimal non-4-colorable graph forces
the complement to be `2`-regular without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 14) :
    Gᶜ.IsRegularOfDegree 2 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact hinc.compl_isRegularOfDegree_two_of_card_eq_seven_of_card_edgeFinset_eq_fourteen hcard hedge

end MinimalBranch

end FourColor.Curriculum.Actual
