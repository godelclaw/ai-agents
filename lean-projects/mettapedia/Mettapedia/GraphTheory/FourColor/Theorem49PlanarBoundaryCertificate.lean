import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryEmbedding

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Boundary-aware graph-level certificate object for the current annulus-shaped Theorem 4.9
route: a plane embedding with boundary of `G` together with a boundary-rooted face peel
certificate on the attached ambient face subtype of that embedding. Unlike the closed-planar
certificate surface, the selected boundary support need not vanish automatically and therefore
remains a separate hypothesis in the annihilator theorem. -/
structure PlanarBoundaryAttachedRootedFacePeelCertificate (G : SimpleGraph V) where
  embedding : PlaneEmbeddingWithBoundary G
  certificate : BoundaryRootedFacePeelCertificate embedding.faces.attach
    (ambientFaceBoundary (allFaces := embedding.faces) embedding.faceBoundary)

/-- Honest graph-level existence target for the boundary-aware attached-face certificate surface.
-/
def AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarBoundaryAttachedRootedFacePeelCertificate G)

theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_iff
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (BoundaryRootedFacePeelCertificate emb.faces.attach
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.embedding, ⟨data.certificate⟩⟩
  · rintro ⟨emb, ⟨cert⟩⟩
    exact ⟨⟨emb, cert⟩⟩

/-- Graph-level boundary-aware annihilator form of the attached-face certificate surface. This is
the exact endpoint naturally reached by the repaired annulus route before any closed-planar
specialization. -/
theorem zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈
      selectedBoundarySupport
        data.embedding.faceBoundary data.embedding.faces data.embedding.faces, z e = 0)
    (horth : ∀ f ∈ data.certificate.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (data.certificate.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.certificate.witnessEdge f))
              (C (data.certificate.witnessEdge f) + γ)
              (data.embedding.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.certificate.witnessEdge f))
              (C (data.certificate.witnessEdge f) + γ)
              (data.embedding.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_boundary_zero_and_attachedBoundaryRootedFacePeelCertificate
    (emb := data.embedding) (C := C) (htait := htait) (z := z)
    (cert := data.certificate) (hzeroBoundary := hzeroBoundary) horth

/-- Graph-level boundary-aware attached-certificate annihilator with local orthogonality supplied
by the Definition 4.8 Kempe-closure generator family. -/
theorem zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈
      selectedBoundarySupport
        data.embedding.faceBoundary data.embedding.faces data.embedding.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily data.embedding.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_attachedBoundaryRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (emb := data.embedding) (C₀ := C₀) (C := C) (htait := htait)
      (hC := hC) (z := z) (cert := data.certificate)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level boundary-aware annihilator form of the attached-face certificate
surface. -/
theorem zero_on_allEdges_of_exists_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ data : PlanarBoundaryAttachedRootedFacePeelCertificate G,
      (∀ e ∈
        selectedBoundarySupport
          data.embedding.faceBoundary data.embedding.faces data.embedding.faces, z e = 0) ∧
      (∀ f ∈ data.certificate.faceOrder,
        ∀ γ, γ ≠ 0 → γ ≠ C (data.certificate.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (data.certificate.witnessEdge f))
                (C (data.certificate.witnessEdge f) + γ)
                (data.embedding.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (data.certificate.witnessEdge f))
                (C (data.certificate.witnessEdge f) + γ)
                (data.embedding.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate
    (data := data) (C := C) (htait := htait) (z := z)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level boundary-aware annihilator form of the attached-face certificate
surface, with local orthogonality supplied by the Definition 4.8 Kempe-closure generator family.
-/
theorem zero_on_allEdges_of_exists_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ data : PlanarBoundaryAttachedRootedFacePeelCertificate G,
      (∀ e ∈
        selectedBoundarySupport
          data.embedding.faceBoundary data.embedding.faces data.embedding.faces, z e = 0) ∧
      AnnihilatesKempeClosureGeneratorFamily data.embedding.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data := data) (C₀ := C₀) (C := C) (htait := htait)
      (hC := hC) (z := z) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

end Mettapedia.GraphTheory.FourColor
