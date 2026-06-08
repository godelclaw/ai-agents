import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Closed-planar version of the boundary-aware well-founded-parent witness-cover package. Since a
genuine plane embedding has empty ambient boundary support, this is the weakest current closed
Step 2 theorem target that still feeds directly into the Theorem 4.9 route without choosing an
explicit numeric height. -/
abbrev PlanarWellFoundedFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  PlanarBoundaryWellFoundedFacePeelWitnessData emb.toPlaneEmbeddingWithBoundary

/-- Graph-level packaging of the weakest current closed-planar well-founded-parent collar-peeling
target. -/
structure PlanarWellFoundedFacePeelWitnessPackage (G : SimpleGraph V) where
  embedding : PlaneEmbedding G
  data : PlanarWellFoundedFacePeelWitnessData embedding

/-- Honest graph-level existence target for the weakest current closed-planar well-founded-parent
peeling package. -/
def AdmitsPlanarWellFoundedFacePeelWitnessData (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarWellFoundedFacePeelWitnessPackage G)

theorem admitsPlanarWellFoundedFacePeelWitnessData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarWellFoundedFacePeelWitnessData G ↔
      ∃ emb : PlaneEmbedding G, Nonempty (PlanarWellFoundedFacePeelWitnessData emb) := by
  constructor
  · rintro ⟨pkg⟩
    exact ⟨pkg.embedding, ⟨pkg.data⟩⟩
  · rintro ⟨emb, ⟨data⟩⟩
    exact ⟨⟨emb, data⟩⟩

theorem PlanarWellFoundedFacePeelWitnessPackage.isPlanar {G : SimpleGraph V}
    (pkg : PlanarWellFoundedFacePeelWitnessPackage G) :
    IsPlanar G :=
  ⟨pkg.embedding⟩

theorem isPlanar_of_admitsPlanarWellFoundedFacePeelWitnessData {G : SimpleGraph V}
    (hG : AdmitsPlanarWellFoundedFacePeelWitnessData G) :
    IsPlanar G := by
  rcases hG with ⟨pkg⟩
  exact pkg.isPlanar

/-- The weakest current closed-planar well-founded-parent collar-peeling package canonically yields
the repaired graph-level certificate object. -/
noncomputable def
    PlanarWellFoundedFacePeelWitnessPackage.toPlanarBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (pkg : PlanarWellFoundedFacePeelWitnessPackage G) :
    PlanarBoundaryRootedFacePeelCertificate G where
  embedding := pkg.embedding
  certificate := pkg.data.toBoundaryRootedFacePeelCertificate

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarWellFoundedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.toPlanarBoundaryRootedFacePeelCertificate⟩

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarWellFoundedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.embedding.toPlaneEmbeddingWithBoundary, ⟨pkg.data⟩⟩

/-- Closed-planar global annihilator form of the weakest current well-founded-parent collar-peeling
package. A genuine plane embedding kills the ambient boundary term automatically, so only the
well-founded parent/witness-cover data and the local orthogonality equations remain. -/
theorem zero_on_allEdges_of_planarWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarWellFoundedFacePeelWitnessData emb)
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
  exact zero_on_allEdges_of_planarBoundaryWellFoundedFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_planarWellFoundedFacePeelWitnessPackage
    {G : SimpleGraph V}
    (pkg : PlanarWellFoundedFacePeelWitnessPackage G)
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
  exact zero_on_allEdges_of_planarWellFoundedFacePeelWitnessData
    (emb := pkg.embedding) (C := C) (htait := htait) (z := z) (data := pkg.data) horth

/-- Existential graph-level closed-planar annihilator form of the weakest current
well-founded-parent collar-peeling package. -/
theorem zero_on_allEdges_of_exists_planarWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ pkg : PlanarWellFoundedFacePeelWitnessPackage G,
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
  exact zero_on_allEdges_of_planarWellFoundedFacePeelWitnessPackage
    (pkg := pkg) (C := C) (htait := htait) (z := z) horth

/-- The root-free interior-dual height-parent package over a genuine closed plane embedding
canonically lowers to the weaker closed-planar well-founded-parent witness-cover package. -/
noncomputable def
    planarWellFoundedFacePeelWitnessPackage_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    PlanarWellFoundedFacePeelWitnessPackage G where
  embedding := emb
  data := planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData data

theorem admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarWellFoundedFacePeelWitnessData G :=
  ⟨planarWellFoundedFacePeelWitnessPackage_of_interiorDualHeightParentPeelData emb data⟩

/-- The root-free interior-dual well-founded-parent package over a genuine closed plane embedding
canonically lowers to the weaker closed-planar well-founded-parent witness-cover package. -/
noncomputable def
    planarWellFoundedFacePeelWitnessPackage_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    PlanarWellFoundedFacePeelWitnessPackage G where
  embedding := emb
  data := planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    data

theorem admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarWellFoundedFacePeelWitnessData G :=
  ⟨planarWellFoundedFacePeelWitnessPackage_of_interiorDualWellFoundedParentPeelData emb data⟩

/-- The strongest current closed-planar interior-dual endpoint canonically lowers to the weaker
closed-planar well-founded-parent witness-cover package. -/
noncomputable def
    planarWellFoundedFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarWellFoundedFacePeelWitnessPackage G :=
  planarWellFoundedFacePeelWitnessPackage_of_interiorDualWellFoundedParentPeelData
    emb data.toInteriorDualWellFoundedParentPeelData

theorem admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarWellFoundedFacePeelWitnessData G :=
  ⟨planarWellFoundedFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data⟩

end Mettapedia.GraphTheory.FourColor
