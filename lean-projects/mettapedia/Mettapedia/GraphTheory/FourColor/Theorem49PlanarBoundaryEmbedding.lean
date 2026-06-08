import Mettapedia.GraphTheory.FourColor.PlanarBoundaryFaceIncidence
import Mettapedia.GraphTheory.FourColor.Theorem49Certificate
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorDualForest

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The annulus-shaped planarity bridge for the current Theorem 4.9 machinery. For a genuine plane
embedding with boundary, an attached-face peel certificate plus boundary vanishing already implies
global vanishing on all graph edges. This matches the actual regime of the annular between-region
`H` in the Goertzel route, where boundary edges have incidence count `1` rather than `2`. -/
theorem zero_on_allEdges_of_boundary_zero_and_attachedBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.attach.biUnion
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary), z e = 0 := by
    refine zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces.attach)
      (faceBoundary := ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
      (cert := cert)
      ?_ ?_ horth
    · intro e
      rw [totalIncidenceCount_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
      exact planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
    · intro e he
      rw [selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] at he
      exact hzeroBoundary e he
  intro e
  apply hzeroSupport e
  rw [biUnion_attach_ambientFaceBoundary_eq
    (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
  simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e

/-- Boundary-aware attached-certificate annihilator with local orthogonality lowered from the
Definition 4.8 Kempe-closure generator family. This is the fixed-embedding form consumed by the
annulus route once the interior-dual forest has supplied an attached face-peel certificate. -/
theorem zero_on_allEdges_of_boundary_zero_and_attachedBoundaryRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (cert : BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.attach.biUnion
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary), z e = 0 := by
    refine
      zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
        (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
        (allFaces := emb.faces.attach)
        (faceBoundary := ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (cert := cert)
        ?_ ?_ ?_
    · intro e
      rw [totalIncidenceCount_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
      exact planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
    · intro e he
      rw [selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] at he
      exact hzeroBoundary e he
    · intro C' hC' f a b hab
      simpa [ambientFaceBoundary] using hgen C' hC' f.1 a b hab
  intro e
  apply hzeroSupport e
  rw [biUnion_attach_ambientFaceBoundary_eq
    (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
  simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e

end Mettapedia.GraphTheory.FourColor
