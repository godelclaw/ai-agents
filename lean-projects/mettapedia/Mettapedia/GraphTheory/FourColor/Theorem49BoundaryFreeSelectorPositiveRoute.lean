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

/-- The same strict-descent selector lane already reaches the full theorem-4.9 synthesis
endpoint once a local unblocked endpoint is available.  No extra residual-boundary or projected
packaging is needed below the annulus-construction surface built by the selector. -/
theorem BoundaryFreeIncidentFaceSelector.theorem49BoundaryRootSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint
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
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
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

/-- Boundary-root parent peel data already exposes a terminal peeled face whose non-witness
remainders lie on the ambient annulus boundary and whose full face boundary stays disjoint from
selected-boundary support, provided a local unblocked interior endpoint exists on the same
embedding. -/
theorem exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ data.peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique
            emb.faceBoundary emb.faces data.hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              data.roots data.hcoverRoots data.hsepRoots)
            data.fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  let selector :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  rcases
    selector.exists_terminal_face_boundary_remainders_and_disjoint_of_strictDescent_and_hasUnblockedInteriorEndpoint
      boundaryData data.fallbackEdge
      (fun f =>
        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots f))
      (by
        simpa [selector] using
          boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
            boundaryData data)
      hEndpoint with
    ⟨f, hfSelector, hremainders, hdisjoint⟩
  have hfData :
      f ∈ data.peelFaces :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_peelFaces_subset
      data hfSelector
  have hselected :
      selector.selectedWitnessEdge data.fallbackEdge f =
        rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f := by
    simpa [selector] using
      boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_selectedWitnessEdge_eq
        data hfSelector
  refine ⟨f, hfData, ?_, hdisjoint⟩
  intro e he
  exact hremainders e (by simpa [selector, hselected] using he)

/-- The raw source-fixed canonical-parent shared-edge cover shell already forces a terminal
peeled face whose non-witness remainders are ambient-boundary edges and whose full face boundary
avoids selected-boundary support, once the same embedding has a local unblocked interior
endpoint. -/
theorem exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
          e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  simpa using
    exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint

/-- The live successor-cycle boundary-order shell already forces the same terminal selected-face
boundary break on the raw canonical-parent shared-edge cover package, once the embedding also
supplies a local unblocked interior endpoint witness. -/
theorem
    exists_terminal_face_boundary_remainders_and_disjoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  simpa [source] using
    exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- The source-fixed canonical-parent shared-edge face-membership shell already forces the same
terminal peeled-face break as soon as the same embedding supplies a local unblocked interior
endpoint witness.  The extra child-membership data strengthens the source package but does not
change the selector-side terminal boundary-break conclusion. -/
theorem
    exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
          e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  simpa using
    exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      hEndpoint

/-- The live successor-cycle boundary-order shell inherits the same selector terminal selected-face
break already on the stronger canonical-parent shared-edge face-membership package, once the
embedding also has a local unblocked interior endpoint witness. -/
theorem
    exists_terminal_face_boundary_remainders_and_disjoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  simpa [source] using
    exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

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

/-- The weaker boundary-root adjacency-distance package already reaches the same selector-side
terminal boundary-break witness because it canonically upgrades to the canonical-parent shell. -/
theorem exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ data.peelFaces,
      (∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique
            emb.faceBoundary emb.faces data.hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              data.roots data.hcoverRoots data.hsepRoots)
            data.fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary) ∧
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  simpa [InteriorDualBoundaryRootAdjDistancePeelData.toInteriorDualBoundaryRootParentPeelData]
    using
      exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
        boundaryData data.toInteriorDualBoundaryRootParentPeelData hEndpoint

theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      boundaryData data.toInteriorDualBoundaryRootParentPeelData hEndpoint

theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootAdjDistancePeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector
      data.boundaryData data.interiorData hEndpoint

/-- The source-fixed canonical-parent shared-edge face-membership shell already reaches the
selector-built height-ordered positive geometry surface on the same embedding once a local
unblocked endpoint exists. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      hEndpoint

/-- The weaker source-fixed canonical-parent shared-edge cover shell already reaches the
selector-built height-ordered positive geometry surface on the same embedding once a local
unblocked endpoint exists. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint

/-- The live successor-cycle boundary-order shell already reaches the same selector-built
height-ordered positive geometry surface on the stronger canonical-parent face-membership
package, once the embedding also supplies a local unblocked endpoint witness. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  simpa [source] using
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- The live successor-cycle boundary-order shell already reaches the same selector-built
height-ordered positive geometry surface on the raw canonical-parent shared-edge cover package,
once the embedding also supplies a local unblocked endpoint witness. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  simpa [source] using
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- Graph-level source-fixed canonical-parent face-membership selector route to the packaged
height-ordered positive geometry surface. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
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
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
        hEndpoint⟩

/-- Graph-level source-fixed canonical-parent raw-cover selector route to the packaged
height-ordered positive geometry surface. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
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
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint⟩

/-- Graph-level successor-cycle boundary-order selector route to the packaged height-ordered
positive geometry surface on the stronger canonical-parent face-membership shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren hEndpoint⟩

/-- Graph-level successor-cycle boundary-order selector route to the packaged height-ordered
positive geometry surface on the canonical-parent raw-cover shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint⟩

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

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      boundaryData data.toInteriorDualBoundaryRootParentPeelData hEndpoint C0 hC0

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector
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

/-- The same source-fixed canonical-parent shared-edge face-membership cover route already reaches
the full theorem-4.9 synthesis endpoint on the same embedding once a local unblocked endpoint is
available. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
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
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
        (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
          source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
        hEndpoint)
      C0 hC0

/-- Source-fixed raw canonical-parent shared-edge cover route through the boundary-free selector.
The parent child-membership field is derived internally from the raw cover plus the ambient
two-incidence bound, so these are the minimal current source-side canonical-parent hypotheses. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint C0 hC0

/-- The same raw-cover source-fixed canonical-parent hypotheses also reach the full theorem-4.9
synthesis endpoint through the boundary-free selector route. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
        (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
          source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
        hEndpoint)
      C0 hC0

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

/-- The same raw-cover source-fixed canonical-parent hypotheses also expose the raw
Definition 4.8 quotient/error package through the boundary-free selector route. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
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
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
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

/-- The same graph-level source-fixed canonical-parent face-membership cover route also reaches
the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
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
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
        hEndpoint C0 hC0⟩

/-- The same graph-level source-fixed canonical-parent face-membership cover route also carries
the raw Definition 4.8 quotient/error package directly once the existential shell provides a
Kirchhoff representative on the selected-boundary endpoint support. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
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
        HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
      hchildren, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
        hEndpoint C0 hC0 hx⟩

/-- Graph-level source-fixed raw canonical-parent shared-edge cover route through the
boundary-free selector.  This is the source-side positive endpoint corresponding to the raw-cover
constructor where child-membership is derived internally. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
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
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint C0 hC0⟩

/-- The same graph-level source-fixed raw canonical-parent shared-edge cover route also reaches
the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
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
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint C0 hC0⟩

/-- The same graph-level source-fixed raw canonical-parent shared-edge cover route also carries
the raw Definition 4.8 quotient/error package directly once the existential shell provides a
Kirchhoff representative on the selected-boundary endpoint support. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
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
        HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
      hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint C0 hC0 hx⟩

/-- The live successor-cycle boundary-order shell reaches the same selector-based positive
projected endpoint already on the stronger canonical-parent shared-edge face-membership package,
as soon as the induced honest source carries that package together with a local unblocked
endpoint witness. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
      hEndpoint C0 hC0

/-- The same successor-cycle canonical-parent face-membership package already reaches the full
theorem-4.9 synthesis endpoint through the selector path. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
      hEndpoint C0 hC0

/-- The same successor-cycle canonical-parent face-membership package also exposes the raw
Definition 4.8 quotient/error route directly through the selector path. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Graph-level successor-cycle boundary-order version of the selector-based positive route from
the stronger canonical-parent shared-edge face-membership cover plus a local unblocked endpoint
witness. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren hEndpoint C0 hC0⟩

/-- Graph-level successor-cycle boundary-order version of the same selector-based positive route
all the way to the full theorem-4.9 synthesis endpoint on the stronger face-membership shell. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren hEndpoint C0 hC0⟩

/-- Graph-level successor-cycle boundary-order version of the same selector-based raw
quotient/error endpoint on the stronger canonical-parent face-membership shell. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren hEndpoint C0 hC0 hx⟩

/-- The actual successor-cycle boundary-order shell reaches the same selector-based positive
projected endpoint as soon as the induced honest source carries the raw canonical-parent
shared-edge cover data and a local unblocked endpoint witness. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hEndpoint C0 hC0

/-- The same successor-cycle canonical-parent raw-cover package already reaches the full
theorem-4.9 synthesis endpoint through the selector path. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hEndpoint C0 hC0

/-- The same successor-cycle canonical-parent raw-cover package also exposes the raw Definition
4.8 quotient/error route directly through the selector path, without passing through residual
boundary packaging. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Graph-level successor-cycle boundary-order version of the selector-based positive route from
the raw canonical-parent shared-edge cover plus a local unblocked endpoint witness. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint C0 hC0⟩

/-- Graph-level successor-cycle boundary-order version of the same selector-based positive route
all the way to the full theorem-4.9 synthesis endpoint. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint C0 hC0⟩

/-- Graph-level successor-cycle boundary-order version of the same selector-based raw
quotient/error endpoint on the canonical-parent raw-cover shell. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint C0 hC0 hx⟩

end Theorem49ForcingInteriorEdgeObstruction

end Mettapedia.GraphTheory.FourColor
