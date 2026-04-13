import Mathlib.Data.ENat.Basic
import FourColor.Curriculum.Actual.EdgeDensity

namespace FourColor.Curriculum.Actual

section TopOnFive

variable {V : Type*} [Fintype V]

/-- If `|V| = 5`, the complete graph on `V` is not 4-colorable.

Source: new theorem via `χ(completeGraph V) = |V|`. -/
theorem top_not_colorable_four_of_card_eq_five
    (hcard : Fintype.card V = 5) :
    ¬ (⊤ : SimpleGraph V).Colorable 4 := by
  intro hcol
  have hχ : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
    simp
  have hle : ((Fintype.card V : ℕ) : ℕ∞) ≤ 4 := by
    simpa [hχ] using
      (hcol.chromaticNumber_le : (⊤ : SimpleGraph V).chromaticNumber ≤ 4)
  have hle' : (5 : ℕ∞) ≤ 4 := by
    simpa [hcard] using hle
  exact (by decide : ¬ ((5 : ℕ∞) ≤ 4)) hle'

/-- If `|V| = 5`, deleting one vertex from the complete graph on `V` yields a 4-colorable induced
graph.

Source: new theorem using the trivial finite-cardinality coloring bound on the complement subtype. -/
theorem top_induce_compl_singleton_colorable_four_of_card_eq_five
    [DecidableEq V]
    (hcard : Fintype.card V = 5) (v : V) :
    ((⊤ : SimpleGraph V).induce ({v}ᶜ)).Colorable 4 := by
  have hcol_card :
      ((⊤ : SimpleGraph V).induce ({v}ᶜ)).Colorable (Fintype.card ({v}ᶜ : Set V)) := by
    simpa using
      (SimpleGraph.colorable_of_fintype (G := (⊤ : SimpleGraph ({v}ᶜ : Set V))))
  have hcard_compl : Fintype.card ({v}ᶜ : Set V) = 4 := by
    calc
      Fintype.card ({v}ᶜ : Set V) = Fintype.card V - Fintype.card ({v} : Set V) := by
        simpa using (Fintype.card_compl_set ({v} : Set V))
      _ = Fintype.card V - 1 := by simp
      _ = 4 := by
        rw [hcard]
  simpa [hcard_compl] using hcol_card

/-- If `|V| = 5`, the complete graph on `V` is vertex-critical non-4-colorable.

Source: new theorem from top non-4-colorability and the one-vertex deletion coloring lemma. -/
theorem top_isVertexCriticalNonColorable_four_of_card_eq_five
    [DecidableEq V]
    (hcard : Fintype.card V = 5) :
    IsVertexCriticalNonColorable (⊤ : SimpleGraph V) 4 := by
  refine ⟨top_not_colorable_four_of_card_eq_five hcard, ?_⟩
  intro v
  exact top_induce_compl_singleton_colorable_four_of_card_eq_five hcard v

/-- If `|V| = 5`, the complete graph on `V` is incidence-critical non-4-colorable.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem top_isIncidenceCriticalNonColorable_four_of_card_eq_five
    [DecidableEq V]
    (hcard : Fintype.card V = 5) :
    IsIncidenceCriticalNonColorable (⊤ : SimpleGraph V) 4 :=
  (top_isVertexCriticalNonColorable_four_of_card_eq_five hcard).toIncidenceCritical_four

end TopOnFive

section Classification

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Five-vertex classification (vertex-critical): on `|V| = 5`, vertex-critical non-4-colorable
graphs are exactly complete graphs.

Source: new theorem combining `EdgeDensity.eq_top_of_card_eq_five` with the complete-graph witness
lemma. -/
theorem isVertexCriticalNonColorable_four_iff_eq_top_of_card_eq_five
    (hcard : Fintype.card V = 5) :
    IsVertexCriticalNonColorable G 4 ↔ G = (⊤ : SimpleGraph V) := by
  refine ⟨fun h => h.eq_top_of_card_eq_five hcard, ?_⟩
  intro htop
  subst htop
  exact top_isVertexCriticalNonColorable_four_of_card_eq_five hcard

/-- Five-vertex classification (incidence-critical): on `|V| = 5`, incidence-critical
non-4-colorable graphs are exactly complete graphs.

Source: new theorem combining `EdgeDensity.eq_top_of_card_eq_five` with the complete-graph witness
lemma and the vertex-to-incidence bridge. -/
theorem isIncidenceCriticalNonColorable_four_iff_eq_top_of_card_eq_five
    (hcard : Fintype.card V = 5) :
    IsIncidenceCriticalNonColorable G 4 ↔ G = (⊤ : SimpleGraph V) := by
  refine ⟨fun h => h.eq_top_of_card_eq_five hcard, ?_⟩
  intro htop
  subst htop
  exact top_isIncidenceCriticalNonColorable_four_of_card_eq_five hcard

end Classification

section LocalStructure

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On five vertices, every vertex-critical non-4-colorable graph has degree `4` at each vertex.

Source: new theorem from `degree ≥ 4` and `degree < |V| = 5`. -/
theorem IsVertexCriticalNonColorable.degree_eq_four_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) (v : V) :
    G.degree v = 4 := by
  have hge : 4 ≤ G.degree v := h.four_le_degree v
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hle : G.degree v ≤ 4 := by
    have hlt5 : G.degree v < 5 := by simpa [hcard] using hlt
    exact Nat.lt_succ_iff.mp hlt5
  exact Nat.le_antisymm hle hge

/-- On five vertices, every incidence-critical non-4-colorable graph has degree `4` at each vertex.

Source: new theorem from `degree ≥ 4` and `degree < |V| = 5`. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_eq_five
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 5) (v : V) :
    G.degree v = 4 := by
  have hge : 4 ≤ G.degree v := h.four_le_degree v
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hle : G.degree v ≤ 4 := by
    have hlt5 : G.degree v < 5 := by simpa [hcard] using hlt
    exact Nat.lt_succ_iff.mp hlt5
  exact Nat.le_antisymm hle hge

/-- On five vertices, deleting all edges incident to a fixed vertex in a vertex-critical
non-4-colorable graph leaves exactly six edges.

Source: new theorem from the five-vertex classification to `⊤`, then edge-delete cardinality. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_deleteIncidenceSet_eq_six_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) (v : V) :
    (G.deleteIncidenceSet v).edgeFinset.card = 6 := by
  have htop : G = (⊤ : SimpleGraph V) :=
    (isVertexCriticalNonColorable_four_iff_eq_top_of_card_eq_five (G := G) hcard).1 h
  subst htop
  have htopcrit : IsVertexCriticalNonColorable (⊤ : SimpleGraph V) 4 :=
    top_isVertexCriticalNonColorable_four_of_card_eq_five hcard
  have hedges : ((⊤ : SimpleGraph V).edgeFinset.card) = 10 :=
    htopcrit.card_edgeFinset_eq_ten_of_card_eq_five hcard
  have hdeg : (⊤ : SimpleGraph V).degree v = 4 :=
    htopcrit.degree_eq_four_of_card_eq_five hcard v
  calc
    ((⊤ : SimpleGraph V).deleteIncidenceSet v).edgeFinset.card
        = ((⊤ : SimpleGraph V).edgeFinset.card) - (⊤ : SimpleGraph V).degree v := by
          simpa using
            (SimpleGraph.card_edgeFinset_deleteIncidenceSet (G := (⊤ : SimpleGraph V)) (x := v))
    _ = 10 - 4 := by rw [hedges, hdeg]
    _ = 6 := by decide

/-- On five vertices, deleting one vertex from a vertex-critical non-4-colorable graph gives an
induced graph with chromatic number exactly `4`.

Source: new theorem from the five-vertex classification to `⊤`, `induce_top`, and complement-card
computation. -/
theorem IsVertexCriticalNonColorable.deleteVertex_chromaticNumber_eq_four_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) (v : V) :
    (G.induce ({v}ᶜ)).chromaticNumber = 4 := by
  have htop : G = (⊤ : SimpleGraph V) :=
    (isVertexCriticalNonColorable_four_iff_eq_top_of_card_eq_five (G := G) hcard).1 h
  subst htop
  have hχ : ((⊤ : SimpleGraph V).induce ({v}ᶜ)).chromaticNumber =
      Fintype.card ({v}ᶜ : Set V) := by
    simp
  have hcard_compl : Fintype.card ({v}ᶜ : Set V) = 4 := by
    calc
      Fintype.card ({v}ᶜ : Set V) = Fintype.card V - Fintype.card ({v} : Set V) := by
        simpa using (Fintype.card_compl_set ({v} : Set V))
      _ = Fintype.card V - 1 := by simp
      _ = 4 := by rw [hcard]
  rwa [hcard_compl] at hχ

/-- On five vertices, deleting one vertex from a vertex-critical non-4-colorable graph is not
3-colorable.

Source: new theorem from the exact chromatic-number computation above. -/
theorem IsVertexCriticalNonColorable.deleteVertex_not_colorable_three_of_card_eq_five
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 5) (v : V) :
    ¬ (G.induce ({v}ᶜ)).Colorable 3 := by
  intro h3
  have hχ4 : (G.induce ({v}ᶜ)).chromaticNumber = 4 :=
    h.deleteVertex_chromaticNumber_eq_four_of_card_eq_five hcard v
  have hle : (G.induce ({v}ᶜ)).chromaticNumber ≤ 3 := h3.chromaticNumber_le
  have : (4 : ℕ∞) ≤ 3 := by
    simpa [hχ4] using hle
  exact (by decide : ¬ ((4 : ℕ∞) ≤ 3)) this

end LocalStructure

end FourColor.Curriculum.Actual
