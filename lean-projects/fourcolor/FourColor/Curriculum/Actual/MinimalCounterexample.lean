import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import FourColor.Curriculum.Actual.ExtremalColoring

namespace FourColor.Curriculum.Actual

variable {V : Type*}

/-- `G` is minimal among graphs that are not `n`-colorable (on the fixed vertex type `V`).

Source: new definition built on Mathlib's graph order and coloring notions. -/
def IsMinimalNonColorable (G : SimpleGraph V) (n : ℕ) : Prop :=
  ¬ G.Colorable n ∧ ∀ ⦃H : SimpleGraph V⦄, H < G → H.Colorable n

namespace IsMinimalNonColorable

variable {G H : SimpleGraph V} {n : ℕ}

/-- Extract the core non-colorability fact from minimality.

Source: new (definition unpacking). -/
theorem not_colorable (h : IsMinimalNonColorable G n) : ¬ G.Colorable n :=
  h.1

/-- Any strict subgraph of a minimal non-colorable graph is `n`-colorable.

Source: new (definition unpacking). -/
theorem colorable_of_lt (h : IsMinimalNonColorable G n) (hHG : H < G) : H.Colorable n :=
  h.2 hHG

/-- Any proper subgraph (with `H ≤ G` and `H ≠ G`) is `n`-colorable.

Source: new (order-theoretic consequence). -/
theorem colorable_of_le_ne (h : IsMinimalNonColorable G n)
    (hHG : H ≤ G) (hne : H ≠ G) : H.Colorable n :=
  h.colorable_of_lt (lt_of_le_of_ne hHG hne)

/-- Deleting a nonempty set of existing edges cannot leave the graph unchanged.

Source: new lemma using `SimpleGraph.deleteEdges_eq_self` from Mathlib. -/
theorem deleteEdges_ne_self_of_subset_nonempty
    {s : Set (Sym2 V)} (hsub : s ⊆ G.edgeSet) (hsne : s.Nonempty) :
    G.deleteEdges s ≠ G := by
  intro hEq
  have hdisj : Disjoint G.edgeSet s :=
    (SimpleGraph.deleteEdges_eq_self (G := G) (s := s)).1 hEq
  rcases hsne with ⟨e, he⟩
  have hin : e ∈ G.edgeSet ∩ s := ⟨hsub he, he⟩
  have : e ∈ (⊥ : Set (Sym2 V)) := hdisj.le_bot hin
  exact this.elim

/-- Edge deletion by a nonempty set of existing edges yields an `n`-colorable graph.

Source: new theorem combining minimality with Mathlib's edge-deletion order lemmas. -/
theorem colorable_deleteEdges_of_subset_nonempty
    (h : IsMinimalNonColorable G n) {s : Set (Sym2 V)}
    (hsub : s ⊆ G.edgeSet) (hsne : s.Nonempty) :
    (G.deleteEdges s).Colorable n := by
  exact h.colorable_of_le_ne
    (hHG := G.deleteEdges_le s)
    (hne := deleteEdges_ne_self_of_subset_nonempty hsub hsne)

/-- Deleting any present edge from a minimal non-colorable graph makes it `n`-colorable.

Source: new theorem. -/
theorem colorable_deleteEdge
    (h : IsMinimalNonColorable G n) {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).Colorable n := by
  refine h.colorable_deleteEdges_of_subset_nonempty ?_ ?_
  · intro e he
    have he' : e = s(u, v) := by simpa using he
    subst he'
    simpa using huv
  · exact ⟨s(u, v), by simp⟩

/-- Deleting the incidence set of an incident vertex makes the graph `n`-colorable.

Source: new theorem using `deleteIncidenceSet` and minimality. -/
theorem colorable_deleteIncidenceSet_of_adj
    (h : IsMinimalNonColorable G n) {u v : V} (huv : G.Adj u v) :
    (G.deleteIncidenceSet u).Colorable n := by
  rw [SimpleGraph.deleteIncidenceSet]
  refine h.colorable_deleteEdges_of_subset_nonempty ?_ ?_
  · exact G.incidenceSet_subset u
  · refine ⟨s(u, v), ?_⟩
    simpa [G.mem_incidenceSet] using huv

end IsMinimalNonColorable

section FourColorSpecialization

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A minimal non-4-colorable graph satisfies the AES dichotomy:
either a `K₅` obstruction exists or the minimum degree is low.

Source: new wrapper specialized from `ExtremalColoring`. -/
theorem IsMinimalNonColorable.k5_or_low_minDegree
    (h : IsMinimalNonColorable G 4) :
    ¬ G.CliqueFree 5 ∨ G.minDegree ≤ 8 * Fintype.card V / 11 :=
  not_colorable_four_forces_k5_or_low_minDegree G h.not_colorable

/-- Embedding-level form of the previous dichotomy for minimal non-4-colorable graphs.

Source: new wrapper specialized from `ExtremalColoring`. -/
theorem IsMinimalNonColorable.k5_embedding_or_low_minDegree
    (h : IsMinimalNonColorable G 4) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) ∨
      G.minDegree ≤ 8 * Fintype.card V / 11 :=
  not_colorable_four_forces_k5_embedding_or_low_minDegree G h.not_colorable

/-- If a minimal non-4-colorable graph has high minimum degree, it must contain a `K₅` embedding.

Source: new wrapper specialized from `ExtremalColoring`. -/
theorem IsMinimalNonColorable.exists_k5_embedding_of_large_minDegree
    (h : IsMinimalNonColorable G 4)
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) :=
  exists_k5_embedding_of_not_colorable_four_and_large_minDegree G h.not_colorable hdeg

end FourColorSpecialization

end FourColor.Curriculum.Actual
