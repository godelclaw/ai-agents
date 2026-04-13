import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card
import FourColor.Curriculum.Actual.MinimalCounterexample

namespace FourColor.Curriculum.Actual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If deleting all edges incident to `v` is `n`-colorable and `deg(v) < n`,
then the original graph is `n`-colorable by recoloring only `v`.

Source: new theorem using Mathlib's `deleteIncidenceSet` API and finite-cardinality lemmas. -/
theorem colorable_of_colorable_deleteIncidenceSet_of_degree_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} {v : V}
    (hcol : (G.deleteIncidenceSet v).Colorable n)
    (hdeg : G.degree v < n) :
    G.Colorable n := by
  classical
  rcases hcol with ⟨C⟩
  let used : Finset (Fin n) := (G.neighborFinset v).image fun w => C w
  have hused_lt : used.card < n := by
    calc
      used.card ≤ (G.neighborFinset v).card := Finset.card_image_le
      _ = G.degree v := by simp
      _ < n := hdeg
  have hused_lt_univ : used.card < (Finset.univ : Finset (Fin n)).card := by
    simpa using hused_lt
  rcases Finset.exists_mem_notMem_of_card_lt_card
      (s := used) (t := (Finset.univ : Finset (Fin n))) hused_lt_univ with
      ⟨c₀, -, hc₀_not_used⟩
  let D : V → Fin n := fun w => if w = v then c₀ else C w
  refine ⟨SimpleGraph.Coloring.mk D ?_⟩
  intro x y hxy
  by_cases hx : x = v
  · by_cases hy : y = v
    · exact ((G.ne_of_adj hxy) (hx.trans hy.symm)).elim
    · have hvy : G.Adj v y := by simpa [hx] using hxy
      have hmem : C y ∈ used := by
        refine Finset.mem_image.mpr ?_
        refine ⟨y, (G.mem_neighborFinset v y).2 hvy, rfl⟩
      have hneq : c₀ ≠ C y := by
        intro hEq
        exact hc₀_not_used (by simpa [hEq] using hmem)
      simpa [D, hx, hy] using hneq
  · by_cases hy : y = v
    · have hvx : G.Adj v x := by simpa [hy] using hxy.symm
      have hmem : C x ∈ used := by
        refine Finset.mem_image.mpr ?_
        refine ⟨x, (G.mem_neighborFinset v x).2 hvx, rfl⟩
      have hneq : C x ≠ c₀ := by
        intro hEq
        exact hc₀_not_used (by simpa [hEq] using hmem)
      simpa [D, hx, hy] using hneq
    · have hxy_del : (G.deleteIncidenceSet v).Adj x y :=
        (SimpleGraph.deleteIncidenceSet_adj (G := G) (x := v) (v₁ := x) (v₂ := y)).2
          ⟨hxy, hx, hy⟩
      simpa [D, hx, hy] using C.valid hxy_del

namespace IsMinimalNonColorable

variable {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- In an edge-minimal non-`n`-colorable graph, any vertex with at least one neighbor
has degree at least `n`.

Source: new theorem combining `MinimalCounterexample` and `VertexRecoloring`. -/
theorem le_degree_of_exists_adj
    (h : IsMinimalNonColorable G n) {v : V} (hadj : ∃ w, G.Adj v w) :
    n ≤ G.degree v := by
  by_contra hlt
  have hdeg : G.degree v < n := Nat.lt_of_not_ge hlt
  rcases hadj with ⟨w, hvw⟩
  have hdel : (G.deleteIncidenceSet v).Colorable n :=
    h.colorable_deleteIncidenceSet_of_adj (u := v) (v := w) hvw
  have hcol : G.Colorable n :=
    colorable_of_colorable_deleteIncidenceSet_of_degree_lt (G := G) hdel hdeg
  exact h.not_colorable hcol

/-- If every vertex has a neighbor, an edge-minimal non-`n`-colorable graph has
minimum degree at least `n`.

Source: new theorem using Mathlib's `le_minDegree_of_forall_le_degree`. -/
theorem le_minDegree_of_forall_exists_adj
    [Nonempty V] (h : IsMinimalNonColorable G n) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    n ≤ G.minDegree :=
  G.le_minDegree_of_forall_le_degree n (fun v => h.le_degree_of_exists_adj (hadj v))

/-- Four-color specialization: each non-isolated vertex has degree at least `4`
in an edge-minimal non-4-colorable graph. -/
theorem four_le_degree_of_exists_adj
    (h : IsMinimalNonColorable G 4) {v : V} (hadj : ∃ w, G.Adj v w) :
    4 ≤ G.degree v :=
  h.le_degree_of_exists_adj hadj

/-- Four-color specialization: if every vertex has a neighbor, then `minDegree ≥ 4`
in an edge-minimal non-4-colorable graph. -/
theorem four_le_minDegree_of_forall_exists_adj
    [Nonempty V] (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    4 ≤ G.minDegree :=
  h.le_minDegree_of_forall_exists_adj hadj

end IsMinimalNonColorable

end FourColor.Curriculum.Actual
