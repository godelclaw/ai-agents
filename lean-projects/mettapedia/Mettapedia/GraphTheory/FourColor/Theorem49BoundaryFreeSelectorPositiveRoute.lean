import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement

/-!
# Boundary-free selector positive route for Theorem 4.9

The selector obstruction layer isolates the strict-descent condition needed to break finite
remainder-dependency cycles.  This file records the corresponding positive route: once a
boundary-free incident-face selector is injective over interior edges and every non-witness
remainder is either ambient-boundary support or the selected witness of a strictly deeper selected
face, it already supplies the height-ordered replacement geometry used by the current projected
Theorem 4.9 endpoint.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ForcingInteriorEdgeObstruction

variable {V : Type*} [DecidableEq V]

/-- A strict-descent boundary-free incident-face selector is already a fixed-embedding
height-ordered replacement source once the purified selected-boundary carrier is nonempty. -/
theorem BoundaryFreeIncidentFaceSelector.theorem49HeightOrderedPositiveProjectedGeometryOn_of_strictDescent
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction
      (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest)
      hCarrier

/-- Local-endpoint form of the strict-descent boundary-free selector route.  The selector supplies
the annulus construction; the endpoint witness supplies the live purified carrier. -/
theorem BoundaryFreeIncidentFaceSelector.theorem49HeightOrderedPositiveProjectedGeometryOn_of_strictDescent_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
      (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest)
      hEndpoint

/-- Direct projected-synthesis form of the strict-descent boundary-free selector route. -/
theorem BoundaryFreeIncidentFaceSelector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction
      (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest)
      hCarrier C0 hC0

/-- Local-endpoint projected-synthesis form of the strict-descent boundary-free selector route. -/
theorem BoundaryFreeIncidentFaceSelector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
      (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest)
      hEndpoint C0 hC0

/-- A strict-descent selector with a local endpoint witness exposes the terminal boundary-break
face without passing through raw carrier nonemptiness. -/
theorem BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_of_strictDescent_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ selector.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  exact
    selector.exists_terminal_face_boundary_remainders_of_interiorEdgeSupport_nonempty
      boundaryData fallbackEdge faceDistance hrest
      (interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint hEndpoint)

/-- A strict-descent selector with a local endpoint witness exposes a terminal selected face whose
non-witness remainders lie on the ambient annulus boundary and whose full face boundary avoids
selected-boundary support. -/
theorem BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_and_disjoint_of_strictDescent_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ selector.peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  rcases
    selector.exists_terminal_face_boundary_remainders_of_strictDescent_and_hasUnblockedInteriorEndpoint
      boundaryData fallbackEdge faceDistance hrest hEndpoint with
    ⟨f, hf, hremainders⟩
  exact ⟨f, hf, hremainders,
    selector.faceBoundary_disjoint_selectedBoundarySupport_of_mem_peelFaces hf⟩

theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  let selector :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  exact
    selector.theorem49HeightOrderedPositiveProjectedGeometryOn_of_strictDescent_and_hasUnblockedInteriorEndpoint
      boundaryData data.fallbackEdge
      (fun f =>
        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots f))
      (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective data)
      (by
        simpa [selector] using
          boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
            boundaryData data)
      hEndpoint

theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      data.boundaryData data.interiorData hEndpoint

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let selector :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  exact
    selector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint
      boundaryData data.fallbackEdge
      (fun f =>
        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots f))
      (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective data)
      (by
        simpa [selector] using
          boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
            boundaryData data)
      hEndpoint C0 hC0

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      data.boundaryData data.interiorData hEndpoint C0 hC0

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      hEndpoint C0 hC0

/-- Source-fixed canonical-parent hypotheses, a local endpoint witness, and a Tait coloring
also expose the raw Definition 4.8 quotient/error package carried by the projected synthesis
endpoint.  This is the fixed-embedding downstream form of the selector-based positive route. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
      hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level source-fixed canonical-parent route through the boundary-free selector.  The
carrier side is stated as the local endpoint witness consumed by the selector construction,
rather than as the raw nonempty selected-boundary carrier. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots)
              source.fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
        hEndpoint C0 hC0⟩

end Theorem49ForcingInteriorEdgeObstruction

end Mettapedia.GraphTheory.FourColor
