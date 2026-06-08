import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The current boundary-embedding abstraction admits the degenerate embedding with one ambient
boundary face containing every edge.  Every edge is then a boundary edge, so the embedding has no
interior support to peel. -/
noncomputable def allEdgesBoundaryPlaneEmbeddingWithBoundary
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    PlaneEmbeddingWithBoundary G where
  Face := PUnit
  faceDecidableEq := inferInstance
  faces := Finset.univ
  faceBoundary := fun _ => Finset.univ
  edge_mem_faceSupport := by
    intro e
    simp
  edge_one_or_two_faces := by
    intro e _he
    left
    simp

theorem selectedBoundarySupport_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_univ
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    selectedBoundarySupport
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faceBoundary
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faces
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faces =
      Finset.univ := by
  ext e
  simp [selectedBoundarySupport, totalIncidenceCount,
    allEdgesBoundaryPlaneEmbeddingWithBoundary]

theorem interiorEdgeSupport_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    interiorEdgeSupport
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faceBoundary
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faces =
      ∅ := by
  ext e
  simp [interiorEdgeSupport, totalIncidenceCount,
    allEdgesBoundaryPlaneEmbeddingWithBoundary]

theorem selectedBoundaryInteriorEdgeEndpointVertices_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    selectedBoundaryInteriorEdgeEndpointVertices
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G) =
      ∅ := by
  simp [selectedBoundaryInteriorEdgeEndpointVertices,
    selectedBoundaryInteriorVertices, verticesAvoidingEdgeSupport,
    interiorEdgeEndpointSupport, edgeEndpointSupport,
    interiorEdgeSupport_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty]

/-- The degenerate all-boundary embedding has an empty attached peel certificate whenever the edge
type is inhabited.  The witness function is never inspected because the face order is empty and
there are no interior edges to cover. -/
noncomputable def emptyAttachedCertificate_allEdgesBoundaryPlaneEmbeddingWithBoundary
    (G : SimpleGraph V) [Fintype G.edgeSet] [Inhabited G.edgeSet] :
    BoundaryRootedFacePeelCertificate
      (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faces.attach
      (ambientFaceBoundary
        (allFaces := (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faces)
        (allEdgesBoundaryPlaneEmbeddingWithBoundary G).faceBoundary) where
  faceOrder := []
  witnessEdge := fun _ => default
  coverInterior := by
    intro e he
    rw [interiorEdgeSupport_ambientFaceBoundary_eq] at he
    rw [interiorEdgeSupport_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty G] at he
    simp at he
  step := by
    intro l₁ l₂ f hsplit
    simp at hsplit

/-- Therefore the graph-level boundary-aware attached-certificate surface is inhabited for every
finite graph with at least one edge, without using any annulus or planar geometry. -/
noncomputable def degeneratePlanarBoundaryAttachedRootedFacePeelCertificate
    (G : SimpleGraph V) [Fintype G.edgeSet] [Inhabited G.edgeSet] :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := allEdgesBoundaryPlaneEmbeddingWithBoundary G
  certificate := emptyAttachedCertificate_allEdgesBoundaryPlaneEmbeddingWithBoundary G

theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_fintype_edgeSet
    (G : SimpleGraph V) [Fintype G.edgeSet] [Inhabited G.edgeSet] :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact ⟨degeneratePlanarBoundaryAttachedRootedFacePeelCertificate G⟩

end Mettapedia.GraphTheory.FourColor
