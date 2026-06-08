import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mettapedia.GraphTheory.PlanarEmbeddingWithBoundary

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

/-- A finite plane embedding of a simple graph, represented only by the finite face set and the
boundary edges of each face. The key closed-surface axiom used by the current four-color route is
that every edge appearing on some face boundary is incident to exactly two faces. -/
structure PlaneEmbedding (G : SimpleGraph V) where
  Face : Type u
  faceDecidableEq : DecidableEq Face
  faces : Finset Face
  faceBoundary : Face → Finset G.edgeSet
  edge_mem_faceSupport : ∀ e : G.edgeSet, e ∈ faces.biUnion faceBoundary
  edge_two_faces :
    ∀ e ∈ faces.biUnion faceBoundary,
      (faces.filter fun f => e ∈ faceBoundary f).card = 2

attribute [instance] PlaneEmbedding.faceDecidableEq

namespace PlaneEmbedding

/-- The edge support of a plane embedding: the union of all face boundaries. -/
def faceSupport {G : SimpleGraph V} (emb : PlaneEmbedding G) : Finset G.edgeSet :=
  emb.faces.biUnion emb.faceBoundary

/-- The number of embedded faces incident to a given edge. -/
def totalFaceIncidenceCount {G : SimpleGraph V} (emb : PlaneEmbedding G) (e : G.edgeSet) : ℕ :=
  (emb.faces.filter fun f => e ∈ emb.faceBoundary f).card

theorem mem_faceSupport {G : SimpleGraph V} (emb : PlaneEmbedding G) (e : G.edgeSet) :
    e ∈ emb.faceSupport := by
  simpa [faceSupport] using emb.edge_mem_faceSupport e

theorem totalFaceIncidenceCount_eq_two_of_mem_faceSupport {G : SimpleGraph V}
    (emb : PlaneEmbedding G) {e : G.edgeSet} (he : e ∈ emb.faceSupport) :
    emb.totalFaceIncidenceCount e = 2 :=
  emb.edge_two_faces e (by simpa [faceSupport] using he)

theorem totalFaceIncidenceCount_eq_two {G : SimpleGraph V}
    (emb : PlaneEmbedding G) (e : G.edgeSet) :
    emb.totalFaceIncidenceCount e = 2 :=
  emb.totalFaceIncidenceCount_eq_two_of_mem_faceSupport (emb.mem_faceSupport e)

theorem totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport {G : SimpleGraph V}
    (emb : PlaneEmbedding G) {e : G.edgeSet} (he : e ∉ emb.faceSupport) :
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
    (emb : PlaneEmbedding G) (e : G.edgeSet) :
    emb.totalFaceIncidenceCount e ≤ 2 := by
  by_cases he : e ∈ emb.faceSupport
  · rw [emb.totalFaceIncidenceCount_eq_two_of_mem_faceSupport he]
  · rw [emb.totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport he]
    omega

end PlaneEmbedding

/-- A closed plane embedding is in particular a plane embedding with boundary in which every edge
is incident to two faces. -/
def PlaneEmbedding.toPlaneEmbeddingWithBoundary {G : SimpleGraph V} (emb : PlaneEmbedding G) :
    PlaneEmbeddingWithBoundary G where
  Face := emb.Face
  faceDecidableEq := emb.faceDecidableEq
  faces := emb.faces
  faceBoundary := emb.faceBoundary
  edge_mem_faceSupport := emb.edge_mem_faceSupport
  edge_one_or_two_faces := by
    intro e he
    exact Or.inr (emb.edge_two_faces e he)

/-- A graph is planar when it admits a finite plane embedding. -/
def IsPlanar (G : SimpleGraph V) : Prop := Nonempty (PlaneEmbedding G)

theorem isPlanar_iff_nonempty_planeEmbedding {G : SimpleGraph V} :
    IsPlanar G ↔ Nonempty (PlaneEmbedding G) :=
  Iff.rfl

theorem exists_planeEmbedding_of_isPlanar {G : SimpleGraph V} (hG : IsPlanar G) :
    Nonempty (PlaneEmbedding G) :=
  hG

end Mettapedia.GraphTheory
