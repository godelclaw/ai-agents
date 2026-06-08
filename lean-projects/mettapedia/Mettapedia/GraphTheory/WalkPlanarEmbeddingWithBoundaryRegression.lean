import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundaryAcyclic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

namespace Mettapedia.GraphTheory

open SimpleGraph
open scoped Classical

namespace WalkPlanarEmbeddingWithBoundaryRegression

private theorem star_sym2_edges_length_le_three {l : List (Sym2 (Fin 4))} (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(0, 1), s(0, 2), s(0, 3)} : Finset (Sym2 (Fin 4))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  have hcard_le := Finset.card_le_card hsubset
  simpa using hcard_le

/-- The three-edge star used to separate the current cyclic edge-list surrogate from the stronger
actual facial closed-walk source interface. -/
def starGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(0, 2), s(0, 3)} : Set (Sym2 (Fin 4)))

def s01 : starGraph.edgeSet := ⟨s(0, 1), by simp [starGraph]⟩

def s02 : starGraph.edgeSet := ⟨s(0, 2), by simp [starGraph]⟩

def s03 : starGraph.edgeSet := ⟨s(0, 3), by simp [starGraph]⟩

theorem s01_ne_s02 : s01 ≠ s02 := by
  intro h
  have := congrArg Subtype.val h
  simp [s01, s02] at this

theorem s01_ne_s03 : s01 ≠ s03 := by
  intro h
  have := congrArg Subtype.val h
  simp [s01, s03] at this

theorem s02_ne_s03 : s02 ≠ s03 := by
  intro h
  have := congrArg Subtype.val h
  simp [s02, s03] at this

def starFaces : Finset Unit := {()}

def starFaceBoundary : Unit → Finset starGraph.edgeSet
  | () => {s01, s02, s03}

theorem star_edge_eq_s01_or_s02_or_s03 (e : starGraph.edgeSet) :
    e = s01 ∨ e = s02 ∨ e = s03 := by
  have h : (e.1 = s(0, 1) ∨ e.1 = s(0, 2) ∨ e.1 = s(0, 3)) ∧ ¬ e.1.IsDiag := by
    simpa [starGraph] using e.2
  rcases h.1 with h01 | h02 | h03
  · exact Or.inl <| Subtype.ext h01
  · exact Or.inr <| Or.inl <| Subtype.ext h02
  · exact Or.inr <| Or.inr <| Subtype.ext h03

/-- A weak boundary-aware embedding whose unique ambient face boundary is the three-star spoke
set. The current cyclic edge-list interface accepts this as a cyclic boundary order because every
consecutive pair of spokes shares the center vertex `0`. -/
def starEmbedding : PlaneEmbeddingWithBoundary starGraph where
  Face := Unit
  faceDecidableEq := inferInstance
  faces := starFaces
  faceBoundary := starFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases star_edge_eq_s01_or_s02_or_s03 e with rfl | rfl | rfl <;>
      exact Finset.mem_biUnion.2 ⟨(), by simp [starFaces], by simp [starFaceBoundary]⟩
  edge_one_or_two_faces := by
    intro e he
    left
    rcases star_edge_eq_s01_or_s02_or_s03 e with rfl | rfl | rfl <;>
      simp [starFaces, starFaceBoundary]

def starOnlyFace : {f // f ∈ starEmbedding.faces} := ⟨(), by simp [starEmbedding, starFaces]⟩

theorem planarEmbeddingBoundaryEdgeEndpointAdj_s01_s02 :
    planarEmbeddingBoundaryEdgeEndpointAdj s01 s02 := by
  refine ⟨s01_ne_s02, 0, ?_, ?_⟩ <;> simp [s01, s02]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_s02_s03 :
    planarEmbeddingBoundaryEdgeEndpointAdj s02 s03 := by
  refine ⟨s02_ne_s03, 0, ?_, ?_⟩ <;> simp [s02, s03]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_s03_s01 :
    planarEmbeddingBoundaryEdgeEndpointAdj s03 s01 := by
  refine ⟨s01_ne_s03.symm, 0, ?_, ?_⟩ <;> simp [s03, s01]

/-- The star embedding satisfies the current cyclic boundary-order interface: the three spokes can
be listed cyclically because every consecutive pair shares the hub vertex `0`. -/
def starCyclicOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData starEmbedding where
  faceBoundaryOrder := fun _ => [s01, s02, s03]
  hchain := by
    intro f
    exact (List.isChain_cons_cons).2
      ⟨planarEmbeddingBoundaryEdgeEndpointAdj_s01_s02,
        (List.isChain_pair).2 planarEmbeddingBoundaryEdgeEndpointAdj_s02_s03⟩
  hnodup := by
    intro f
    simp [s01_ne_s02, s01_ne_s03, s02_ne_s03]
  hmem := by
    intro f e
    rcases star_edge_eq_s01_or_s02_or_s03 e with rfl | rfl | rfl <;>
      simp [starEmbedding, starFaceBoundary]
  hwrap := by
    intro f first last hfirst hlast
    have hfirst' : first = s01 := by simpa using hfirst.symm
    have hlast' : last = s03 := by simpa using hlast.symm
    subst first
    subst last
    exact planarEmbeddingBoundaryEdgeEndpointAdj_s03_s01

theorem nonempty_cyclicOrderedFaceBoundaryData_starEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData starEmbedding) := by
  exact ⟨starCyclicOrderedFaceBoundaryData⟩

theorem nonempty_faceBoundaryClosedRunGeometry_starEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry starEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_starEmbedding

theorem nonempty_faceBoundaryClosedVertexWalkGeometry_starEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry starEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_starEmbedding

theorem star_no_triangle {a b c : Fin 4} :
    ¬ (starGraph.Adj a b ∧ starGraph.Adj b c ∧ starGraph.Adj c a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [starGraph]

theorem star_edges_length_le_three {v w : Fin 4} (p : starGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub : ∀ e ∈ p.edges, e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3) := by
    intro e he
    have hedge : e ∈ starGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3)) ∧ ¬ e.IsDiag := by
      simpa [starGraph] using hedge
    exact h.1
  have hle_edges : p.edges.length ≤ 3 :=
    star_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

/-- The star graph is acyclic: any cyclic walk would have length exactly `3`, hence would give a
triangle, but the three-star has no triangle. -/
theorem starGraph_isAcyclic : starGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := star_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil => simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil => simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil => simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact star_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

/-- The same star embedding cannot admit the stronger actual closed-walk source interface: a
nonempty closed trail in an acyclic graph would have to be a path, hence nil. -/
theorem not_nonempty_faceBoundaryClosedWalkGeometry_starEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry starEmbedding) := by
  exact
    not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- The current cyclic ordered edge-list surface is strictly weaker than the honest actual-walk
source interface. -/
theorem exists_embedding_withCyclicOrderedFaceBoundaryData_withoutClosedWalkGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary starGraph,
      Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  exact ⟨starEmbedding, nonempty_cyclicOrderedFaceBoundaryData_starEmbedding,
    not_nonempty_faceBoundaryClosedWalkGeometry_starEmbedding⟩

/-- The same strictness already persists after lowering to the bundled cyclic edge-only run shell.
-/
theorem exists_embedding_withClosedRunGeometry_withoutClosedWalkGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary starGraph,
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  exact ⟨starEmbedding, nonempty_faceBoundaryClosedRunGeometry_starEmbedding,
    not_nonempty_faceBoundaryClosedWalkGeometry_starEmbedding⟩

/-- The explicit cyclic edge/vertex walk surrogate is also strictly weaker than the honest actual
facial closed-walk source interface. -/
theorem exists_embedding_withClosedVertexWalkGeometry_withoutClosedWalkGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary starGraph,
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  exact ⟨starEmbedding, nonempty_faceBoundaryClosedVertexWalkGeometry_starEmbedding,
    not_nonempty_faceBoundaryClosedWalkGeometry_starEmbedding⟩

end WalkPlanarEmbeddingWithBoundaryRegression

end Mettapedia.GraphTheory
