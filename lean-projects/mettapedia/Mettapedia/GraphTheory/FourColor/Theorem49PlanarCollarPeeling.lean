import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Closed-planar version of the boundary-aware finite collar-layer witness-cover package. Since a
genuine plane embedding has empty ambient boundary support, this is the most paper-shaped current
closed Step 2 target: peeled faces are grouped into finitely many nested collars. -/
abbrev PlanarCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  PlanarBoundaryCollarLayerFacePeelWitnessData emb.toPlaneEmbeddingWithBoundary

/-- Graph-level packaging of the closed-planar finite collar-layer target. -/
structure PlanarCollarLayerFacePeelWitnessPackage (G : SimpleGraph V) where
  embedding : PlaneEmbedding G
  data : PlanarCollarLayerFacePeelWitnessData embedding

/-- Honest graph-level existence target for the closed-planar finite collar-layer package. -/
def AdmitsPlanarCollarLayerFacePeelWitnessData (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarCollarLayerFacePeelWitnessPackage G)

/-- Closed-planar form of the weaker local explicit-remainder collar target. -/
abbrev PlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    emb.toPlaneEmbeddingWithBoundary

/-- Honest graph-level existence target for the weaker local explicit-remainder collar data. -/
def AdmitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, Nonempty (PlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)

/-- Closed-planar form of the stronger geometry-facing relative-boundary collar target. This keeps
the actual remainder-frontier boundary in the theorem-layer collar data, but packages it over a
genuine plane embedding of `G`. -/
abbrev PlanarRelativeBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  RelativeBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Honest graph-level existence target for the stronger relative-boundary collar data. -/
def AdmitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, Nonempty (PlanarRelativeBoundaryCollarLayerFacePeelWitnessData emb)

/-- Closed-planar form of the explicit-remainder collar target. -/
abbrev PlanarRemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  RemainderBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Honest graph-level existence target for the explicit-remainder collar data. -/
def AdmitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, Nonempty (PlanarRemainderBoundaryCollarLayerFacePeelWitnessData emb)

theorem admitsPlanarCollarLayerFacePeelWitnessData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarCollarLayerFacePeelWitnessData G ↔
      ∃ emb : PlaneEmbedding G, Nonempty (PlanarCollarLayerFacePeelWitnessData emb) := by
  constructor
  · rintro ⟨pkg⟩
    exact ⟨pkg.embedding, ⟨pkg.data⟩⟩
  · rintro ⟨emb, ⟨data⟩⟩
    exact ⟨⟨emb, data⟩⟩

theorem PlanarCollarLayerFacePeelWitnessPackage.isPlanar {G : SimpleGraph V}
    (pkg : PlanarCollarLayerFacePeelWitnessPackage G) :
    IsPlanar G :=
  ⟨pkg.embedding⟩

theorem isPlanar_of_admitsPlanarCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (hG : AdmitsPlanarCollarLayerFacePeelWitnessData G) :
    IsPlanar G := by
  rcases hG with ⟨pkg⟩
  exact pkg.isPlanar

/-- A closed-planar collar-layer package canonically yields the repaired graph-level certificate
object via the intermediate height-ordered witness-cover interface. -/
noncomputable def
    PlanarCollarLayerFacePeelWitnessPackage.toPlanarBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (pkg : PlanarCollarLayerFacePeelWitnessPackage G) :
    PlanarBoundaryRootedFacePeelCertificate G where
  embedding := pkg.embedding
  certificate := pkg.data.toHeightOrderedFacePeelWitnessData.toBoundaryRootedFacePeelCertificate

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.toPlanarBoundaryRootedFacePeelCertificate⟩

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨pkg⟩
  exact ⟨pkg.embedding.toPlaneEmbeddingWithBoundary, ⟨pkg.data⟩⟩

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨⟨emb,
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericRelativeBoundaryCollarLayerFacePeelWitnessData
      (emb := emb.toPlaneEmbeddingWithBoundary) data⟩⟩

theorem admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toRelativeBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toRemainderBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData G ↔
      AdmitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData G := by
  constructor
  · exact
      admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData
  · exact
      admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G :=
  admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData
    (admitsPlanarRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarRemainderBoundaryCollarLayerFacePeelWitnessData
      hG)

theorem
    admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨⟨emb,
      planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data⟩⟩

/-- Closed-planar global annihilator form of the finite collar-layer interface. A genuine plane
embedding kills the ambient boundary term automatically, so only the nested-collar data and the
local orthogonality equations remain. -/
theorem zero_on_allEdges_of_planarCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarCollarLayerFacePeelWitnessData emb)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Closed-planar global annihilator form of the stronger relative-boundary collar target. This is
the current closed graph-level theorem surface closest to the paper's actual nested-collar peel. -/
theorem zero_on_allEdges_of_planarRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarRelativeBoundaryCollarLayerFacePeelWitnessData emb)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Closed-planar global annihilator form of the explicit-remainder collar target. -/
theorem zero_on_allEdges_of_planarRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Closed-planar global annihilator form of the weaker local explicit-remainder collar target. -/
theorem zero_on_allEdges_of_planarLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb.toPlaneEmbeddingWithBoundary)
    (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_planarCollarLayerFacePeelWitnessPackage
    {G : SimpleGraph V}
    (pkg : PlanarCollarLayerFacePeelWitnessPackage G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (horth : ∀ i f, f ∈ pkg.data.layerFaces i →
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
  exact zero_on_allEdges_of_planarCollarLayerFacePeelWitnessData
    (emb := pkg.embedding) (C := C) (htait := htait) (z := z) (data := pkg.data) horth

/-- Existential graph-level closed-planar annihilator form of the finite collar-layer package. -/
theorem zero_on_allEdges_of_exists_planarCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ pkg : PlanarCollarLayerFacePeelWitnessPackage G,
      ∀ i f, f ∈ pkg.data.layerFaces i →
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
  exact zero_on_allEdges_of_planarCollarLayerFacePeelWitnessPackage
    (pkg := pkg) (C := C) (htait := htait) (z := z) horth

/-- Existential graph-level closed-planar annihilator form of the stronger relative-boundary collar
target. -/
theorem zero_on_allEdges_of_exists_planarRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbedding G,
      ∃ data : PlanarRelativeBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ i f, f ∈ data.layerFaces i →
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
  rcases hdata with ⟨emb, data, horth⟩
  exact zero_on_allEdges_of_planarRelativeBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data) horth

/-- Existential graph-level closed-planar annihilator form of the explicit-remainder collar
target. -/
theorem zero_on_allEdges_of_exists_planarRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbedding G,
      ∃ data : PlanarRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ i f, f ∈ data.layerFaces i →
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
  rcases hdata with ⟨emb, data, horth⟩
  exact zero_on_allEdges_of_planarRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data) horth

/-- The closed-planar height-ordered witness-cover package canonically groups into finitely many
collar layers by equal height. -/
noncomputable def
    planarCollarLayerFacePeelWitnessPackage_of_planarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarHeightOrderedFacePeelWitnessData emb) :
    PlanarCollarLayerFacePeelWitnessPackage G where
  embedding := emb
  data := planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData data

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarHeightOrderedFacePeelWitnessData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨pkg⟩
  exact ⟨planarCollarLayerFacePeelWitnessPackage_of_planarHeightOrderedFacePeelWitnessData
    pkg.embedding pkg.data⟩

/-- The strongest current closed-planar interior-dual endpoint canonically lowers to the finite
closed-planar collar-layer package. -/
noncomputable def
    planarCollarLayerFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarCollarLayerFacePeelWitnessPackage G where
  embedding := emb
  data := planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    (emb := emb.toPlaneEmbeddingWithBoundary) data

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G :=
  ⟨planarCollarLayerFacePeelWitnessPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data⟩

/-- The weakest current closed-planar root-free interior-dual package canonically lowers to the
finite collar-layer package. -/
noncomputable def
    planarCollarLayerFacePeelWitnessPackage_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    PlanarCollarLayerFacePeelWitnessPackage G where
  embedding := emb
  data :=
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G :=
  ⟨planarCollarLayerFacePeelWitnessPackage_of_interiorDualWellFoundedParentPeelData emb data⟩

end Mettapedia.GraphTheory.FourColor
