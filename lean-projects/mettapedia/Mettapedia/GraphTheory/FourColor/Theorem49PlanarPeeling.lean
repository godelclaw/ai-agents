import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Closed-planar version of the boundary-aware height-sorted witness-cover package. Since a
genuine plane embedding has empty ambient boundary support, this is the weakest current closed
Step 2 theorem target that still feeds directly into the Theorem 4.9 route. -/
abbrev PlanarHeightOrderedFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  PlanarBoundaryHeightOrderedFacePeelWitnessData emb.toPlaneEmbeddingWithBoundary

/-- Graph-level packaging of the weakest current closed-planar collar-peeling target. -/
structure PlanarHeightOrderedFacePeelWitnessPackage (G : SimpleGraph V) where
  embedding : PlaneEmbedding G
  data : PlanarHeightOrderedFacePeelWitnessData embedding

/-- Honest graph-level existence target for the weakest current closed-planar peeling package. -/
def AdmitsPlanarHeightOrderedFacePeelWitnessData (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarHeightOrderedFacePeelWitnessPackage G)

theorem admitsPlanarHeightOrderedFacePeelWitnessData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarHeightOrderedFacePeelWitnessData G ↔
      ∃ emb : PlaneEmbedding G, Nonempty (PlanarHeightOrderedFacePeelWitnessData emb) := by
  constructor
  · rintro ⟨pkg⟩
    exact ⟨pkg.embedding, ⟨pkg.data⟩⟩
  · rintro ⟨emb, ⟨data⟩⟩
    exact ⟨⟨emb, data⟩⟩

theorem PlanarHeightOrderedFacePeelWitnessPackage.isPlanar {G : SimpleGraph V}
    (pkg : PlanarHeightOrderedFacePeelWitnessPackage G) :
    IsPlanar G :=
  ⟨pkg.embedding⟩

theorem isPlanar_of_admitsPlanarHeightOrderedFacePeelWitnessData {G : SimpleGraph V}
    (hG : AdmitsPlanarHeightOrderedFacePeelWitnessData G) :
    IsPlanar G := by
  rcases hG with ⟨pkg⟩
  exact pkg.isPlanar

/-- The weakest current closed-planar collar-peeling package canonically yields the repaired
graph-level certificate object. -/
noncomputable def
    PlanarHeightOrderedFacePeelWitnessPackage.toPlanarBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (pkg : PlanarHeightOrderedFacePeelWitnessPackage G) :
    PlanarBoundaryRootedFacePeelCertificate G where
  embedding := pkg.embedding
  certificate := pkg.data.toBoundaryRootedFacePeelCertificate

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarHeightOrderedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.toPlanarBoundaryRootedFacePeelCertificate⟩

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarHeightOrderedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.embedding.toPlaneEmbeddingWithBoundary, ⟨pkg.data⟩⟩

/-- Closed-planar global annihilator form of the weakest current collar-peeling package. A genuine
plane embedding kills the ambient boundary term automatically, so only the height-sorted
witness-cover data and the local orthogonality equations remain. -/
theorem zero_on_allEdges_of_planarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarHeightOrderedFacePeelWitnessData emb)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 := by
    intro e he
    rw [planeEmbedding_selectedBoundarySupport_eq_empty emb] at he
    simp at he
  exact zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_planarHeightOrderedFacePeelWitnessPackage
    {G : SimpleGraph V}
    (pkg : PlanarHeightOrderedFacePeelWitnessPackage G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (horth : ∀ f ∈ pkg.data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (pkg.data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (pkg.data.witnessEdge f))
              (C (pkg.data.witnessEdge f) + γ)
              (pkg.embedding.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (pkg.data.witnessEdge f))
              (C (pkg.data.witnessEdge f) + γ)
              (pkg.embedding.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarHeightOrderedFacePeelWitnessData
    (emb := pkg.embedding) (C := C) (htait := htait) (z := z) (data := pkg.data) horth

/-- Existential graph-level closed-planar annihilator form of the weakest current collar-peeling
package. -/
theorem zero_on_allEdges_of_exists_planarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ pkg : PlanarHeightOrderedFacePeelWitnessPackage G,
      ∀ f ∈ pkg.data.peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (pkg.data.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (pkg.data.witnessEdge f))
                (C (pkg.data.witnessEdge f) + γ)
                (pkg.embedding.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (pkg.data.witnessEdge f))
                (C (pkg.data.witnessEdge f) + γ)
                (pkg.embedding.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨pkg, horth⟩
  exact zero_on_allEdges_of_planarHeightOrderedFacePeelWitnessPackage
    (pkg := pkg) (C := C) (htait := htait) (z := z) horth

/-- The root-free interior-dual height-parent package over a genuine closed plane embedding
canonically lowers to the weaker closed-planar witness-cover package. -/
noncomputable def
    planarHeightOrderedFacePeelWitnessPackage_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    PlanarHeightOrderedFacePeelWitnessPackage G where
  embedding := emb
  data := planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData data

theorem admitsPlanarHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarHeightOrderedFacePeelWitnessData G :=
  ⟨planarHeightOrderedFacePeelWitnessPackage_of_interiorDualHeightParentPeelData emb data⟩

/-- The strongest current closed-planar interior-dual endpoint canonically lowers to the weaker
closed-planar witness-cover package. -/
noncomputable def
    planarHeightOrderedFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarHeightOrderedFacePeelWitnessPackage G :=
  planarHeightOrderedFacePeelWitnessPackage_of_interiorDualHeightParentPeelData
    emb data.toInteriorDualHeightParentPeelData

theorem admitsPlanarHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarHeightOrderedFacePeelWitnessData G :=
  ⟨planarHeightOrderedFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data⟩

end Mettapedia.GraphTheory.FourColor
