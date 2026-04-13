import Mathlib.Combinatorics.SimpleGraph.Finite
import FourColor.Curriculum.Actual.VertexRecoloring
import FourColor.Curriculum.Actual.ExtremalColoring

namespace FourColor.Curriculum.Actual

variable {V : Type*}

/-- `G` is incidence-critical non-`n`-colorable if:
`G` is not `n`-colorable, but deleting all edges incident to any vertex gives an `n`-colorable
graph.

Source: new definition built on Mathlib's `deleteIncidenceSet`. -/
def IsIncidenceCriticalNonColorable
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  ¬ G.Colorable n ∧ ∀ v : V, (G.deleteIncidenceSet v).Colorable n

namespace IsIncidenceCriticalNonColorable

variable {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- Extract the non-colorability component.

Source: new (definition unpacking). -/
theorem not_colorable (h : IsIncidenceCriticalNonColorable G n) : ¬ G.Colorable n :=
  h.1

/-- Every vertex-incidence deletion is `n`-colorable.

Source: new (definition unpacking). -/
theorem colorable_deleteIncidenceSet
    (h : IsIncidenceCriticalNonColorable G n) (v : V) :
    (G.deleteIncidenceSet v).Colorable n :=
  h.2 v

section Finite

variable [Fintype V] [DecidableEq V]

/-- In an incidence-critical non-`n`-colorable graph, every vertex has degree at least `n`.

Source: new theorem via `VertexRecoloring.colorable_of_colorable_deleteIncidenceSet_of_degree_lt`. -/
theorem le_degree (h : IsIncidenceCriticalNonColorable G n) (v : V) :
    n ≤ G.degree v := by
  by_contra hlt
  have hdeg : G.degree v < n := Nat.lt_of_not_ge hlt
  have hcol : G.Colorable n :=
    colorable_of_colorable_deleteIncidenceSet_of_degree_lt
      (G := G) (h.colorable_deleteIncidenceSet v) hdeg
  exact h.not_colorable hcol

/-- In a nonempty incidence-critical non-`n`-colorable graph, minimum degree is at least `n`.

Source: new theorem using Mathlib's `le_minDegree_of_forall_le_degree`. -/
theorem le_minDegree [Nonempty V] (h : IsIncidenceCriticalNonColorable G n) :
    n ≤ G.minDegree :=
  G.le_minDegree_of_forall_le_degree n (fun v => h.le_degree v)

/-- If `n > 0`, every vertex has a neighbor in an incidence-critical non-`n`-colorable graph.

Source: new theorem via Mathlib's `degree_pos_iff_exists_adj`. -/
theorem exists_adj_of_pos (h : IsIncidenceCriticalNonColorable G n) (hn : 0 < n) (v : V) :
    ∃ w, G.Adj v w := by
  have hdeg_pos : 0 < G.degree v := lt_of_lt_of_le hn (h.le_degree v)
  exact (G.degree_pos_iff_exists_adj v).1 hdeg_pos

/-- If `n > 0`, every vertex is in the support of an incidence-critical non-`n`-colorable graph.

Source: new theorem via Mathlib's `degree_pos_iff_mem_support`. -/
theorem mem_support_of_pos (h : IsIncidenceCriticalNonColorable G n) (hn : 0 < n) (v : V) :
    v ∈ G.support := by
  have hdeg_pos : 0 < G.degree v := lt_of_lt_of_le hn (h.le_degree v)
  exact (G.degree_pos_iff_mem_support v).1 hdeg_pos

end Finite

end IsIncidenceCriticalNonColorable

namespace IsMinimalNonColorable

variable {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- If every vertex has a neighbor, edge-minimal non-`n`-colorability implies
incidence-critical non-`n`-colorability.

Source: new bridge theorem from `MinimalCounterexample` to `IncidenceCritical`. -/
theorem toIncidenceCritical
    (h : IsMinimalNonColorable G n) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    IsIncidenceCriticalNonColorable G n := by
  refine ⟨h.not_colorable, ?_⟩
  intro v
  rcases hadj v with ⟨w, hvw⟩
  exact h.colorable_deleteIncidenceSet_of_adj (u := v) (v := w) hvw

/-- Re-derived min-degree bound via the incidence-critical bridge.

Source: new theorem (alternate route, useful for API composition). -/
theorem le_minDegree_of_forall_exists_adj_via_incidence
    [Fintype V] [DecidableEq V] [Nonempty V]
    (h : IsMinimalNonColorable G n) (hadj : ∀ v : V, ∃ w, G.Adj v w) :
    n ≤ G.minDegree :=
  (h.toIncidenceCritical hadj).le_minDegree

end IsMinimalNonColorable

section FourColorSpecialization

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Four-color specialization: incidence-critical non-4-colorable graphs have degree at least `4`
at every vertex.

Source: new specialization from `IsIncidenceCriticalNonColorable.le_degree`. -/
theorem IsIncidenceCriticalNonColorable.four_le_degree
    (h : IsIncidenceCriticalNonColorable G 4) (v : V) :
    4 ≤ G.degree v :=
  h.le_degree v

/-- Four-color specialization: in nonempty incidence-critical non-4-colorable graphs,
minimum degree is at least `4`.

Source: new specialization from `IsIncidenceCriticalNonColorable.le_minDegree`. -/
theorem IsIncidenceCriticalNonColorable.four_le_minDegree
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4) :
    4 ≤ G.minDegree :=
  h.le_minDegree

/-- Four-color + incidence-criticality inherits the standard AES/K₅ dichotomy.

Source: new wrapper through `ExtremalColoring`. -/
theorem IsIncidenceCriticalNonColorable.k5_or_low_minDegree
    (h : IsIncidenceCriticalNonColorable G 4) :
    ¬ G.CliqueFree 5 ∨ G.minDegree ≤ 8 * Fintype.card V / 11 :=
  not_colorable_four_forces_k5_or_low_minDegree G h.not_colorable

/-- Embedding-level form of the AES/K₅ dichotomy for incidence-critical non-4-colorable graphs.

Source: new wrapper through `ExtremalColoring`. -/
theorem IsIncidenceCriticalNonColorable.k5_embedding_or_low_minDegree
    (h : IsIncidenceCriticalNonColorable G 4) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) ∨
      G.minDegree ≤ 8 * Fintype.card V / 11 :=
  not_colorable_four_forces_k5_embedding_or_low_minDegree G h.not_colorable

/-- Combined structural consequence: either a `K₅` obstruction exists, or the min-degree sits in
the explicit interval forced by incidence-criticality and AES.

Source: new theorem combining local and extremal constraints. -/
theorem IsIncidenceCriticalNonColorable.k5_or_minDegree_window
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4) :
    ¬ G.CliqueFree 5 ∨
      (4 ≤ G.minDegree ∧ G.minDegree ≤ 8 * Fintype.card V / 11) := by
  rcases h.k5_or_low_minDegree with hk5 | hlow
  · exact Or.inl hk5
  · exact Or.inr ⟨h.four_le_minDegree, hlow⟩

/-- Any nonempty incidence-critical non-4-colorable finite graph has at least five vertices.

Source: new cardinality consequence from `minDegree ≥ 4` and `minDegree < |V|`. -/
theorem IsIncidenceCriticalNonColorable.card_verts_ge_five
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4) :
    5 ≤ Fintype.card V := by
  have h4 : 4 ≤ G.minDegree := h.four_le_minDegree
  have hlt : G.minDegree < Fintype.card V := G.minDegree_lt_card
  exact Nat.succ_le_of_lt (lt_of_le_of_lt h4 hlt)

/-- Under `K₅`-freeness, a nonempty incidence-critical non-4-colorable finite graph has at least
six vertices.

Source: new finite-size sharpening from local-critical lower bounds plus AES upper bounds. -/
theorem IsIncidenceCriticalNonColorable.card_verts_ge_six_of_cliqueFree
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4) (hfree : G.CliqueFree 5) :
    6 ≤ Fintype.card V := by
  have hge5 : 5 ≤ Fintype.card V := h.card_verts_ge_five
  have hne5 : Fintype.card V ≠ 5 := by
    intro hcard5
    have hlow : G.minDegree ≤ 8 * Fintype.card V / 11 := by
      rcases h.k5_or_low_minDegree with hk5 | hlow
      · exact False.elim (hk5 hfree)
      · exact hlow
    have hlow3 : G.minDegree ≤ 3 := by
      simpa [hcard5] using hlow
    have hhigh : 4 ≤ G.minDegree := h.four_le_minDegree
    have : 4 ≤ 3 := hhigh.trans hlow3
    exact (Nat.not_succ_le_self 3) this
  have hgt5 : 5 < Fintype.card V := lt_of_le_of_ne hge5 (by simpa [eq_comm] using hne5)
  exact Nat.succ_le_of_lt hgt5

/-- Embedding-level version of the previous finite-size sharpening. -/
theorem IsIncidenceCriticalNonColorable.card_verts_ge_six_of_no_k5_embedding
    [Nonempty V] (h : IsIncidenceCriticalNonColorable G 4)
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G)) :
    6 ≤ Fintype.card V := by
  have hfree : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff (G := G) (n := 5)).2 hK5
  exact h.card_verts_ge_six_of_cliqueFree hfree

end FourColorSpecialization

end FourColor.Curriculum.Actual
