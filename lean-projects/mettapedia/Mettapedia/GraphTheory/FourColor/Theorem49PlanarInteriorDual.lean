import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarWellFoundedPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The weakest current embedding-side Step 2 package: a genuine plane embedding together with the
boundary-root adjacency-distance interior-dual data that the remaining annulus argument is now
expected to construct. -/
abbrev PlanarInteriorDualBoundaryRootAdjDistancePeelData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary

/-- The weakest current root-free interior-dual package over a genuine plane embedding. This asks
only for a well-founded parent relation in the chosen interior-dual spanning forest together with
the parent-shared-edge face-membership cover condition. -/
abbrev PlanarInteriorDualWellFoundedParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbedding G) :=
  InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary

/-- The honest remaining weakest graph-level Step 2 target after the planarity repair: there
exists a genuine plane embedding of `G` together with the boundary-root adjacency-distance
interior-dual peeling data expected from the annulus argument. -/
def AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, Nonempty (PlanarInteriorDualBoundaryRootAdjDistancePeelData emb)

/-- Honest graph-level closed-planar target for the weaker root-free well-founded-parent
interior-dual package. -/
def AdmitsPlanarInteriorDualWellFoundedParentPeelData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbedding G, Nonempty (PlanarInteriorDualWellFoundedParentPeelData emb)

theorem admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G ↔
      ∃ emb : PlaneEmbedding G,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :=
  Iff.rfl

/-- The weakest current embedding-side Step 2 package canonically yields the repaired graph-level
certificate object. This is the direct bridge from the interior-dual annulus-facing endpoint to the
planarity-facing certificate endpoint. -/
noncomputable def
    planarBoundaryRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    PlanarBoundaryRootedFacePeelCertificate G :=
  { embedding := emb
    certificate := data.toBoundaryRootedFacePeelCertificate }

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  exact admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarCollarLayerFacePeelWitnessData
    (admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      emb data)

theorem admitsPlanarInteriorDualWellFoundedParentPeelData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    AdmitsPlanarInteriorDualWellFoundedParentPeelData G := by
  exact ⟨emb, ⟨data.toInteriorDualWellFoundedParentPeelData⟩⟩

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualWellFoundedParentPeelData emb) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  exact admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarCollarLayerFacePeelWitnessData
    (admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      emb data)

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  exact ⟨emb.toPlaneEmbeddingWithBoundary, ⟨
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data⟩⟩

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarWellFoundedFacePeelWitnessData
    (admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      emb data)

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact ⟨emb.toPlaneEmbeddingWithBoundary, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data⟩⟩

theorem isPlanar_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    IsPlanar G := by
  rcases hG with ⟨emb, _data⟩
  exact ⟨emb⟩

theorem admitsPlanarHeightOrderedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data

theorem admitsPlanarWellFoundedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data

theorem admitsPlanarInteriorDualWellFoundedParentPeelData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarInteriorDualWellFoundedParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarInteriorDualWellFoundedParentPeelData_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data

theorem admitsPlanarWellFoundedFacePeelWitnessData_of_admitsPlanarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    emb data

theorem
    admitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data⟩⟩

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualWellFoundedParentPeelData
        hG)

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  exact admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarCollarLayerFacePeelWitnessData
    (admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualWellFoundedParentPeelData
      hG)

theorem admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarBoundaryRootedFacePeelCertificate_of_admitsPlanarCollarLayerFacePeelWitnessData
    (admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      emb data)

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G :=
  admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarHeightOrderedFacePeelWitnessData
    (admitsPlanarHeightOrderedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
      hG)

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarWellFoundedFacePeelWitnessData
    (admitsPlanarWellFoundedFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
      hG)

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data

theorem admitsPlanarCollarLayerFacePeelWitnessData_of_admitsPlanarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact admitsPlanarCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    emb data

/-- Closed-planar global annihilator form of the weaker root-free interior-dual package. A genuine
plane embedding kills the ambient boundary term automatically, so only the well-founded parent
relation, the child face-membership cover condition, and the local orthogonality equations remain. -/
theorem zero_on_allEdges_of_planarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarInteriorDualWellFoundedParentPeelData emb)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                  data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  let localData :=
    planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data
  have horth' :
      ∀ i f, f ∈ localData.layerFaces i →
        ∀ γ, γ ≠ 0 → γ ≠ C (localData.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (localData.witnessEdge f))
                (C (localData.witnessEdge f) + γ)
                (emb.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (localData.witnessEdge f))
                (C (localData.witnessEdge f) + γ)
                (emb.faceBoundary f.1)) = 0 := by
    intro i f hfi γ hγ0 hγd
    have hf : f ∈ data.peelFaces :=
      data.mem_peelFaces_of_mem_layer_toLocalRemainderBoundaryCollarLayerFacePeelWitnessData hfi
    exact horth f hf γ hγ0 <| by
      simpa using hγd
  exact zero_on_allEdges_of_planarLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := localData) (horth := horth')

/-- Global graph-edge annihilator form of the weakest current embedding-side Step 2 package. A
genuine plane embedding kills the ambient boundary term automatically, so the weakest annulus-side
adjacency-plus-distance data already suffices for the current Theorem 4.9 route. -/
theorem zero_on_allEdges_of_planarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbedding G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
            data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  let collarData :=
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      (emb := emb.toPlaneEmbeddingWithBoundary) data
  have horth' :
      ∀ i f, f ∈ collarData.layerFaces i →
        ∀ γ, γ ≠ 0 → γ ≠ C (collarData.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (collarData.witnessEdge f))
                (C (collarData.witnessEdge f) + γ)
                (emb.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (collarData.witnessEdge f))
                (C (collarData.witnessEdge f) + γ)
                (emb.faceBoundary f.1)) = 0 := by
    intro i f hfi γ hγ0 hγd
    have hf :
        f ∈
          (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
            (emb := emb.toPlaneEmbeddingWithBoundary) data).peelFaces :=
      (Finset.mem_filter.1 hfi).1
    exact horth f hf γ hγ0 (by simpa [collarData] using hγd)
  exact zero_on_allEdges_of_planarCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := collarData) (horth := horth')

/-- Existential graph-level form of the weakest current annulus-facing Step 2 endpoint. Once such
embedding-side adjacency-distance data exists, the current Theorem 4.9 route annihilates `z`
globally. -/
theorem zero_on_allEdges_of_exists_planarInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbedding G,
      ∃ data : PlanarInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                data.hcoverRoots data.hsepRoots)
              data.fallbackEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, horth⟩
  exact zero_on_allEdges_of_planarInteriorDualBoundaryRootAdjDistancePeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data) horth

theorem zero_on_allEdges_of_exists_planarInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbedding G,
      ∃ data : PlanarInteriorDualWellFoundedParentPeelData emb,
        ∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              data.parentFace data.fallbackEdge data.hparentAdj f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, horth⟩
  exact zero_on_allEdges_of_planarInteriorDualWellFoundedParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data) horth

end Mettapedia.GraphTheory.FourColor
