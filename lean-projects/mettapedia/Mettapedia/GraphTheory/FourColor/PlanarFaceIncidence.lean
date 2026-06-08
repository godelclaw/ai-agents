import Mettapedia.GraphTheory.PlanarEmbedding
import Mettapedia.GraphTheory.FourColor.FaceIncidence

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- For a genuine plane embedding, the generic ambient-face incidence count used in the four-color
route is exactly the embedding's own face-incidence count. -/
theorem planeEmbedding_totalIncidenceCount_eq_totalFaceIncidenceCount
    {G : SimpleGraph V} (emb : PlaneEmbedding G) (e : G.edgeSet) :
    totalIncidenceCount emb.faceBoundary emb.faces e = emb.totalFaceIncidenceCount e :=
  rfl

/-- Every edge on an embedded face boundary is incident to exactly two embedded faces in the
generic ambient-face sense used by the four-color development. -/
theorem planeEmbedding_totalIncidenceCount_eq_two_of_mem_faceSupport
    {G : SimpleGraph V} (emb : PlaneEmbedding G) {e : G.edgeSet}
    (he : e ∈ emb.faceSupport) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 2 := by
  simpa [planeEmbedding_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_eq_two_of_mem_faceSupport he

/-- Embedded edges outside the face support have zero ambient face incidence. -/
theorem planeEmbedding_totalIncidenceCount_eq_zero_of_not_mem_faceSupport
    {G : SimpleGraph V} (emb : PlaneEmbedding G) {e : G.edgeSet}
    (he : e ∉ emb.faceSupport) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 0 := by
  simpa [planeEmbedding_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_eq_zero_of_not_mem_faceSupport he

/-- In a genuine closed plane embedding, every graph edge is incident to exactly two faces in the
generic ambient-face sense used by the four-color development. -/
theorem planeEmbedding_totalIncidenceCount_eq_two
    {G : SimpleGraph V} (emb : PlaneEmbedding G) (e : G.edgeSet) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 2 := by
  simpa [planeEmbedding_totalIncidenceCount_eq_totalFaceIncidenceCount] using
    emb.totalFaceIncidenceCount_eq_two e

/-- Closed plane embeddings satisfy the exact ambient two-face incidence hypothesis on their full
face support. -/
theorem planeEmbedding_totalIncidenceCount_eq_two_on_biUnion
    {G : SimpleGraph V} (emb : PlaneEmbedding G) :
    ∀ e ∈ emb.faces.biUnion emb.faceBoundary, totalIncidenceCount emb.faceBoundary emb.faces e = 2 := by
  intro e he
  exact planeEmbedding_totalIncidenceCount_eq_two_of_mem_faceSupport emb
    (by simpa [PlaneEmbedding.faceSupport] using he)

/-- Closed plane embeddings satisfy the ambient at-most-two-faces incidence bound required by the
generic face-peeling infrastructure. -/
theorem planeEmbedding_totalIncidenceCount_le_two
    {G : SimpleGraph V} (emb : PlaneEmbedding G) :
    ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2 := by
  intro e
  rw [planeEmbedding_totalIncidenceCount_eq_two emb e]

/-- A closed plane embedding has no ambient boundary edges: every selected boundary support for the
full face set is empty. -/
theorem planeEmbedding_selectedBoundarySupport_eq_empty
    {G : SimpleGraph V} (emb : PlaneEmbedding G) :
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces = ∅ := by
  exact selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
    emb.faceBoundary emb.faces emb.faces
    (planeEmbedding_totalIncidenceCount_eq_two_on_biUnion emb)

/-- In a closed plane embedding, every edge on some face boundary is an interior edge in the
generic ambient-face model, so the interior-edge support coincides with the full face support. -/
theorem planeEmbedding_interiorEdgeSupport_eq_faceSupport
    {G : SimpleGraph V} (emb : PlaneEmbedding G) :
    interiorEdgeSupport emb.faceBoundary emb.faces = emb.faceSupport := by
  ext e
  constructor
  · intro he
    exact (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 he |>.1
  · intro he
    exact (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).2
      ⟨by simpa [PlaneEmbedding.faceSupport] using he,
        planeEmbedding_totalIncidenceCount_eq_two_of_mem_faceSupport emb he⟩

/-- Every graph edge lies in the generic interior-edge support coming from a genuine closed plane
embedding. -/
theorem planeEmbedding_mem_interiorEdgeSupport
    {G : SimpleGraph V} (emb : PlaneEmbedding G) (e : G.edgeSet) :
    e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  rw [planeEmbedding_interiorEdgeSupport_eq_faceSupport emb]
  exact emb.mem_faceSupport e

end Mettapedia.GraphTheory.FourColor
