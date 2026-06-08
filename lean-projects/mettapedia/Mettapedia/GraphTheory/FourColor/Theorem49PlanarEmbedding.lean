import Mettapedia.GraphTheory.FourColor.PlanarFaceIncidence
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryEmbedding

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A plane embedding provides the missing connection from an actual planar graph to the current
Theorem 4.9 certificate machinery. Once a boundary-rooted face peel certificate is constructed for
the faces of the embedding, the annihilator conclusion applies to every edge on an embedded face
boundary. -/
theorem zero_on_faceSupport_of_boundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces emb.faceBoundary)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f)) = 0) :
    ∀ e ∈ emb.faceSupport, z e = 0 := by
  simpa [PlaneEmbedding.faceSupport] using
    zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate_of_totalIncidenceCount_eq_two
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces) (faceBoundary := emb.faceBoundary)
      (cert := cert)
      (hcount := planeEmbedding_totalIncidenceCount_eq_two_on_biUnion emb)
      horth

/-- A genuine closed plane embedding covers every graph edge by face boundaries. So once the
boundary-rooted face peel certificate exists on that embedding, the Theorem 4.9 annihilator
conclusion holds on every graph edge, not only on a selected ambient support subset. -/
theorem zero_on_allEdges_of_boundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces emb.faceBoundary)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f)) = 0) :
    ∀ e, z e = 0 := by
  intro e
  exact zero_on_faceSupport_of_boundaryRootedFacePeelCertificate
    (emb := emb) (C := C) (htait := htait) (z := z) (cert := cert) horth e (emb.mem_faceSupport e)

/-- Since a closed plane embedding has no ambient boundary edges, its full face support is exactly
the generic interior-edge support. The certificate conclusion can therefore be read directly on
the interior edges used by the abstract interior-dual graph. -/
theorem zero_on_interiorEdgeSupport_of_boundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces emb.faceBoundary)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f)) = 0) :
    ∀ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, z e = 0 := by
  simpa [planeEmbedding_interiorEdgeSupport_eq_faceSupport emb] using
    zero_on_faceSupport_of_boundaryRootedFacePeelCertificate
      (emb := emb) (C := C) (htait := htait) (z := z) (cert := cert) horth

/-- The interior-edge formulation is global for a genuine closed plane embedding, because every
graph edge belongs to the embedding's interior-edge support. -/
theorem zero_on_allEdges_of_interiorEdgeSupport_boundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces emb.faceBoundary)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f)) = 0) :
    ∀ e, z e = 0 := by
  intro e
  exact zero_on_interiorEdgeSupport_of_boundaryRootedFacePeelCertificate
    (emb := emb) (C := C) (htait := htait) (z := z) (cert := cert) horth e
    (planeEmbedding_mem_interiorEdgeSupport emb e)

/-- The attached-face form of the planarity bridge, matching the current generic interior-dual
certificate endpoint. This is the theorem that connects a genuine plane embedding directly to the
certificate objects produced by the Step 2 interior-dual wrappers. -/
theorem zero_on_allEdges_of_attachedBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 := by
    intro e he
    rw [planeEmbedding_selectedBoundarySupport_eq_empty emb] at he
    simp at he
  exact zero_on_allEdges_of_boundary_zero_and_attachedBoundaryRootedFacePeelCertificate
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z)
    (cert := cert) (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
