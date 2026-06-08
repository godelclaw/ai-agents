import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

/-- A finite plane embedding with boundary. Every graph edge lies on at least one face boundary,
and each edge is incident to either one or two faces. This is the ambient shape needed for annular
between-regions in the four-color route. -/
structure PlaneEmbeddingWithBoundary (G : SimpleGraph V) where
  Face : Type u
  faceDecidableEq : DecidableEq Face
  faces : Finset Face
  faceBoundary : Face → Finset G.edgeSet
  edge_mem_faceSupport : ∀ e : G.edgeSet, e ∈ faces.biUnion faceBoundary
  edge_one_or_two_faces :
    ∀ e ∈ faces.biUnion faceBoundary,
      (faces.filter fun f => e ∈ faceBoundary f).card = 1 ∨
        (faces.filter fun f => e ∈ faceBoundary f).card = 2

attribute [instance] PlaneEmbeddingWithBoundary.faceDecidableEq

namespace PlaneEmbeddingWithBoundary

/-- The edge support of a plane embedding with boundary: the union of all face boundaries. -/
def faceSupport {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Finset G.edgeSet :=
  emb.faces.biUnion emb.faceBoundary

/-- The number of embedded faces incident to a given edge. -/
def totalFaceIncidenceCount {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (e : G.edgeSet) : ℕ :=
  (emb.faces.filter fun f => e ∈ emb.faceBoundary f).card

theorem mem_faceSupport {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (e : G.edgeSet) :
    e ∈ emb.faceSupport := by
  simpa [faceSupport] using emb.edge_mem_faceSupport e

theorem totalFaceIncidenceCount_eq_one_or_two_of_mem_faceSupport {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet} (he : e ∈ emb.faceSupport) :
    emb.totalFaceIncidenceCount e = 1 ∨ emb.totalFaceIncidenceCount e = 2 :=
  emb.edge_one_or_two_faces e (by simpa [faceSupport] using he)

theorem totalFaceIncidenceCount_pos {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    0 < emb.totalFaceIncidenceCount e := by
  unfold totalFaceIncidenceCount
  rcases Finset.mem_biUnion.1 (emb.mem_faceSupport e) with ⟨f, hf, hfe⟩
  exact Finset.card_pos.2 ⟨f, Finset.mem_filter.2 ⟨hf, hfe⟩⟩

theorem totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet} (he : e ∉ emb.faceSupport) :
    emb.totalFaceIncidenceCount e = 0 := by
  unfold totalFaceIncidenceCount
  have hfilter : emb.faces.filter (fun f => e ∈ emb.faceBoundary f) = ∅ := by
    ext f
    constructor
    · intro hf
      exact False.elim <| he <| Finset.mem_biUnion.2
        ⟨f, (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩
    · intro hf
      simp at hf
  simp [hfilter]

theorem totalFaceIncidenceCount_le_two {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    emb.totalFaceIncidenceCount e ≤ 2 := by
  rcases emb.totalFaceIncidenceCount_eq_one_or_two_of_mem_faceSupport (emb.mem_faceSupport e) with
    hone | htwo
  · rw [hone]
    omega
  · rw [htwo]

end PlaneEmbeddingWithBoundary

end Mettapedia.GraphTheory
