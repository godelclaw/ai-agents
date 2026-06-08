import Mettapedia.GraphTheory.PlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.FourColor.FaceIncidence

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- For a boundary-aware plane embedding, the generic ambient-face incidence count used in the
four-color route is exactly the embedding's own face-incidence count. -/
theorem planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    totalIncidenceCount emb.faceBoundary emb.faces e = emb.totalFaceIncidenceCount e :=
  rfl

theorem planeEmbeddingWithBoundary_totalIncidenceCount_eq_zero_of_not_mem_faceSupport
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) {e : G.edgeSet}
    (he : e ∉ emb.faceSupport) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 0 := by
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport he

theorem planeEmbeddingWithBoundary_totalIncidenceCount_pos
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (e : G.edgeSet) :
    0 < totalIncidenceCount emb.faceBoundary emb.faces e := by
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_pos e

theorem planeEmbeddingWithBoundary_totalIncidenceCount_le_two
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2 := by
  intro e
  simpa [planeEmbeddingWithBoundary_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_le_two e

end Mettapedia.GraphTheory.FourColor
