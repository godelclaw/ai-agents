import Mettapedia.GraphTheory.FourColor.Theorem49PlanarEmbedding

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The remaining graph-level geometric object for the current Theorem 4.9 route: a genuine plane
embedding of `G` together with a boundary-rooted face peel certificate on the attached ambient
face subtype used by the current interior-dual machinery. Constructing this object from the actual
planar geometry is now the honest live gap in the formalization. -/
structure PlanarBoundaryRootedFacePeelCertificate (G : SimpleGraph V) where
  embedding : PlaneEmbedding G
  certificate : BoundaryRootedFacePeelCertificate embedding.faces.attach
    (ambientFaceBoundary (allFaces := embedding.faces) embedding.faceBoundary)

/-- The honest remaining graph-level existence target for the current Theorem 4.9 route. -/
def AdmitsPlanarBoundaryRootedFacePeelCertificate (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarBoundaryRootedFacePeelCertificate G)

theorem admitsPlanarBoundaryRootedFacePeelCertificate_iff
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G ↔
      ∃ emb : PlaneEmbedding G,
        Nonempty (BoundaryRootedFacePeelCertificate emb.faces.attach
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.embedding, ⟨data.certificate⟩⟩
  · rintro ⟨emb, ⟨cert⟩⟩
    exact ⟨⟨emb, cert⟩⟩

theorem PlanarBoundaryRootedFacePeelCertificate.isPlanar {G : SimpleGraph V}
    (data : PlanarBoundaryRootedFacePeelCertificate G) :
    IsPlanar G :=
  ⟨data.embedding⟩

theorem isPlanar_of_admitsPlanarBoundaryRootedFacePeelCertificate {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryRootedFacePeelCertificate G) :
    IsPlanar G := by
  rcases hG with ⟨data⟩
  exact data.isPlanar

/-- Graph-level form of the current Theorem 4.9 annihilator route. Once a planar graph is equipped
with a genuine plane embedding and a boundary-rooted face peel certificate on the attached ambient
face subtype of that embedding, the existing certificate machinery forces the target edge function
to vanish globally. -/
theorem zero_on_allEdges_of_planarBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (data : PlanarBoundaryRootedFacePeelCertificate G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (horth : ∀ f ∈ data.certificate.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (data.certificate.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.certificate.witnessEdge f))
              (C (data.certificate.witnessEdge f) + γ)
              (data.embedding.faceBoundary f))
            z
            (polarizedFaceGenerator C
              (C (data.certificate.witnessEdge f))
              (C (data.certificate.witnessEdge f) + γ)
              (data.embedding.faceBoundary f)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_attachedBoundaryRootedFacePeelCertificate
    (emb := data.embedding) (C := C) (htait := htait) (z := z)
    (cert := data.certificate) horth

/-- Existential graph-level form of the current Theorem 4.9 annihilator route. This packages the
remaining planarity-side gap at the level of `G` itself rather than as separate embedding and
certificate arguments. -/
theorem zero_on_allEdges_of_exists_planarBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ data : PlanarBoundaryRootedFacePeelCertificate G,
      ∀ f ∈ data.certificate.faceOrder,
        ∀ γ, γ ≠ 0 → γ ≠ C (data.certificate.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (data.certificate.witnessEdge f))
                (C (data.certificate.witnessEdge f) + γ)
                (data.embedding.faceBoundary f))
              z
              (polarizedFaceGenerator C
                (C (data.certificate.witnessEdge f))
                (C (data.certificate.witnessEdge f) + γ)
                (data.embedding.faceBoundary f)) = 0) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨data, horth⟩
  exact zero_on_allEdges_of_planarBoundaryRootedFacePeelCertificate
    (data := data) (C := C) (htait := htait) (z := z) horth

end Mettapedia.GraphTheory.FourColor
