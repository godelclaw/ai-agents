import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Positive same-embedding endpoint for the constructive source route.  It packages the
non-vacuous theorem-4.9 synthesis together with the corrected projected Definition 4.8 spanning
statements on the same boundary-aware embedding. -/
structure Theorem49BoundaryRootNonemptyProjectedSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C0 : G.EdgeColoring Color) : Prop where
  nonemptySynthesis : Theorem49BoundaryRootNonemptySynthesis emb C0
  projectedSubspace_eq_planarBoundaryZeroSubmodule :
    projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb
  projectedFamilySpan_eq_planarBoundaryZeroSubmodule :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
      planarBoundaryZeroSubmodule emb

/-- Route-facing package for the raw Definition 4.8 quotient/error conclusion at a fixed
boundary-aware embedding.  It combines a Kirchhoff-valid raw finite-generator representative
with a decomposition of the original Kirchhoff chain by a boundary-kernel error. -/
abbrev Theorem49BoundaryRawQuotientErrorPackage {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (C0 : G.EdgeColoring Color)
    (x : G.edgeSet → Color) : Prop :=
  (∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
    (terms : Set (G.edgeSet → Color)) ⊆
        kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
      coeff.support ⊆ terms ∧
        (∑ y ∈ terms, coeff y • y) ∈
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) =
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x) ∧
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryError ∈
                kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                  LinearMap.ker
                    (boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
              (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x

/-- The positive projected synthesis endpoint still carries the raw Kirchhoff representative and
boundary-kernel error decomposition supplied by the underlying theorem-4.9 synthesis package.
This is the route-facing access point for downstream geometric source arguments, so they need not
reach back into the raw projection layer. -/
theorem
    Theorem49BoundaryRootNonemptyProjectedSynthesis.rawKirchhoffRepresentative_and_boundaryKernelDecomposition
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C0 : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    ⟨h.nonemptySynthesis.synthesis.rawKirchhoffRepresentative hx,
      h.nonemptySynthesis.synthesis.rawBoundaryKernelDecomposition hx⟩

/-- Height-ordered witness-cover data gives the positive same-embedding endpoint as soon as the
selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  refine
    { nonemptySynthesis := ?_
      projectedSubspace_eq_planarBoundaryZeroSubmodule :=
        projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
          emb data C0 hC0
      projectedFamilySpan_eq_planarBoundaryZeroSubmodule :=
        span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
          emb data C0 hC0 }
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
          (G := G) data C0 hC0
      carrier_nonempty := hCarrier }

/-- Height-ordered witness-cover data also give the route-facing raw quotient/error conclusion as
soon as the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Finite collar-layer witness-cover data gives the positive same-embedding endpoint as soon as
the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  refine
    { nonemptySynthesis := ?_
      projectedSubspace_eq_planarBoundaryZeroSubmodule :=
        projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
          emb data C0 hC0
      projectedFamilySpan_eq_planarBoundaryZeroSubmodule :=
        span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
          emb data C0 hC0 }
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
          (G := G) data C0 hC0
      carrier_nonempty := hCarrier }

/-- Finite collar-layer witness-cover data also give the route-facing raw quotient/error
conclusion as soon as the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Canonical-parent boundary-root interior-dual data gives the positive projected endpoint on
the same embedding. The construction passes through the height-ordered witness surface induced by
the parent package, keeping the selected-boundary carrier hypothesis explicit. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G)
      (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
        data.toInteriorDualHeightParentPeelData)
      C0 hC0 hCarrier

/-- Canonical-parent boundary-root interior-dual data also give the route-facing raw quotient/
error conclusion once the purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Two-sided annulus-root parent data gives the same positive projected endpoint on the same
embedding.  The annulus boundary split is retained in the input surface, but the proved endpoint
still depends only on the induced interior parent payload together with a nonempty purified
carrier. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      (G := G) data.interiorData C0 hC0 hCarrier

/-- Two-sided annulus-root parent data also give the route-facing raw quotient/error conclusion
once the purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Primitive same-embedding projected endpoint from an annulus boundary split plus generic
boundary-root interior-dual parent data. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G)
      (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
        boundaryData interiorData)
      C0 hC0 hCarrier

/-- Closed-walk source lowering for the carrier-based projected endpoint on the parent route. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G)
      (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
        source interiorData)
      C0 hC0 hCarrier

/-- Graph-level primitive projected endpoint from an annulus boundary split plus generic
boundary-root interior-dual parent data, together with a nonempty purified carrier on that
embedding. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, boundaryData, interiorData, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
        (G := G) boundaryData interiorData C0 hC0 hCarrier⟩

/-- Graph-level closed-walk-source lowering for the carrier-based projected endpoint on the
parent route. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, interiorData, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
        (G := G) source interiorData C0 hC0 hCarrier⟩

/-- Fixed-embedding source-to-Theorem-4.9 composition for the parent-oriented sufficiency branch.
Starting with the raw closed-walk annulus source, the source boundary-face roots and canonical
parent map build the interior-dual parent package and then the nonempty projected synthesis
endpoint. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
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
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      (G := G)
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      C0 hC0 hCarrier

/-- Graph-level source-to-Theorem-4.9 composition for the parent-oriented sufficiency branch.
The hypotheses are the same concrete source-fixed parent obligations as the fixed-embedding
version, with the selected-boundary purified carrier nonempty on that embedding. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
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
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hchildren, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
        hCarrier C0 hC0⟩

/-- Canonical source witness choice gives the positive same-embedding endpoint.  The canonical
choice first builds the one-collar annulus geometry, whose repaired previous-boundary witness
surface yields the finite collar-layer witness-cover package used by the projection layer. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hchoice with ⟨choice⟩
  let collar : PlanarBoundaryAnnulusCollarGeometry emb :=
    choice.toPlanarBoundaryAnnulusCollarGeometry
  let previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
    collar.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
      choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) previous.toPlanarBoundaryCollarLayerFacePeelWitnessData C0 hC0 hCarrier

/-- Graph-level positive endpoint from an honest closed-walk source with canonical witness choice
and a nonempty selected-boundary-purified carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, hchoice, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        source hchoice hCarrier C0 hC0⟩

/-- Same-boundary one-collar source geometry gives the positive same-embedding endpoint.  The
source-boundary equality keeps this theorem aligned with the geometric construction surface. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1)
    (hboundary :
      data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let _ := hboundary
  let previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
    data.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one hnum
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) previous.toPlanarBoundaryCollarLayerFacePeelWitnessData C0 hC0 hCarrier

/-- Graph-level positive endpoint from an honest closed-walk source with same-boundary one-collar
geometry and a nonempty selected-boundary-purified carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, source, data, hnum, hboundary, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        source data hnum hboundary hCarrier C0 hC0⟩

/-- Route-facing successor-cycle positive endpoint from canonical witness choice and a nonempty
selected-boundary-purified carrier.  The successor-cycle boundary shell is lowered to the honest
closed-walk source before applying the same-embedding projected synthesis package. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice, hCarrier⟩ C0 hC0

/-- Route-facing successor-cycle positive endpoint from same-boundary one-collar geometry and a
nonempty selected-boundary-purified carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundary, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, data, hnum, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundary, hCarrier⟩ C0 hC0

/-- Canonical source witness choice reaches the corrected projected Definition 4.8 spanning
statement through the height-ordered witness surface.  The raw Kempe-generator span is not used
as a boundary-zero target here; the projected span is the one that lies in the selected-boundary
zero submodule. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Canonical source witness choice reaches the corrected projected Definition 4.8 spanning
statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from canonical source witness choice, via the
height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from canonical source witness choice, via the
finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- The local at-most-one source criterion reaches the corrected projected Definition 4.8
spanning statement through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- The local at-most-one source criterion reaches the corrected projected Definition 4.8
spanning statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from the local at-most-one source criterion, via
the height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from the local at-most-one source criterion, via
the finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Same-boundary one-collar source geometry reaches the corrected projected Definition 4.8
spanning statement through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Same-boundary one-collar source geometry reaches the corrected projected Definition 4.8
spanning statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from same-boundary one-collar source geometry,
via the height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Family-level projected generator spanning from same-boundary one-collar source geometry,
via the finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

/-- Successor-cycle source data with a canonical witness choice on the extracted annulus split
lowers to the honest closed-walk source package used by the projected spanning bridge. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact ⟨emb, source, by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hchoice⟩

/-- Successor-cycle source data with the local cardinal at-most-one criterion lowers to the
honest closed-walk source package used by the projected spanning bridge. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact ⟨emb, source, fallbackEdge, hfallback, hatMost, by
    intro f e he hi
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundaryRest f he hi⟩

/-- Successor-cycle source data with a same-boundary one-collar geometry lowers to the honest
closed-walk source package used by the projected spanning bridge. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundary⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact ⟨emb, source, data, hnum, by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary⟩

/-- Successor-cycle source plus canonical witness choice reaches the corrected projected
Definition 4.8 spanning statement through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0

/-- Successor-cycle source plus canonical witness choice reaches the corrected projected
Definition 4.8 spanning statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus canonical witness
choice, via the height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus canonical witness
choice, via the finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0

/-- Successor-cycle source plus the local at-most-one criterion reaches the corrected projected
Definition 4.8 spanning statement through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

/-- Successor-cycle source plus the local at-most-one criterion reaches the corrected projected
Definition 4.8 spanning statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus the local
at-most-one criterion, via the height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus the local
at-most-one criterion, via the finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

/-- Successor-cycle source plus same-boundary one-collar geometry reaches the corrected
projected Definition 4.8 spanning statement through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0

/-- Successor-cycle source plus same-boundary one-collar geometry reaches the corrected
projected Definition 4.8 spanning statement through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus same-boundary
one-collar geometry, via the height-ordered witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0

/-- Family-level projected generator spanning from successor-cycle source plus same-boundary
one-collar geometry, via the finite collar-layer witness surface. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0

/-- Canonical source witness choice gives a raw Definition 4.8 generator-subspace preimage for
each concrete boundary-zero Kirchhoff chain, through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives a raw Definition 4.8 generator-subspace preimage for
each concrete boundary-zero Kirchhoff chain, through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives raw Definition 4.8 generator-subspace preimages
for concrete boundary-zero Kirchhoff chains, through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives raw Definition 4.8 generator-subspace preimages
for concrete boundary-zero Kirchhoff chains, through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives raw Definition 4.8 generator-subspace
preimages for concrete boundary-zero Kirchhoff chains, through the height-ordered witness
surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives raw Definition 4.8 generator-subspace
preimages for concrete boundary-zero Kirchhoff chains, through the finite collar-layer witness
surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives raw Definition 4.8
generator-subspace preimages through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives raw Definition 4.8
generator-subspace preimages through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives raw Definition 4.8
generator-subspace preimages through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives raw Definition 4.8
generator-subspace preimages through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives raw Definition 4.8
generator-subspace preimages through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives raw Definition 4.8
generator-subspace preimages through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C0,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives a finite raw Definition 4.8 generator sum whose
selected-boundary projection is any concrete boundary-zero Kirchhoff chain, through the
height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives a finite raw Definition 4.8 generator sum whose
selected-boundary projection is any concrete boundary-zero Kirchhoff chain, through the finite
collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives finite raw Definition 4.8 generator sums for
concrete boundary-zero Kirchhoff chains, through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives finite raw Definition 4.8 generator sums for
concrete boundary-zero Kirchhoff chains, through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives finite raw Definition 4.8 generator sums for
concrete boundary-zero Kirchhoff chains, through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives finite raw Definition 4.8 generator sums for
concrete boundary-zero Kirchhoff chains, through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives finite raw Definition 4.8
generator sums through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives finite raw Definition 4.8
generator sums through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives finite raw Definition 4.8
generator sums through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives finite raw Definition 4.8
generator sums through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives finite raw Definition
4.8 generator sums through the height-ordered witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives finite raw Definition
4.8 generator sums through the finite collar-layer witness surface. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice reaches the projected-source separation theorem for the
concrete boundary-zero Kirchhoff target through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice reaches the projected-source separation theorem through the
finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice reaches the projected-source separation
theorem through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice reaches the projected-source separation
theorem through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion reaches the projected-source separation theorem through
the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion reaches the projected-source separation theorem through
the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion reaches the projected-source
separation theorem through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion reaches the projected-source
separation theorem through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry reaches the projected-source separation theorem
through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry reaches the projected-source separation theorem
through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry reaches the projected-source
separation theorem through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry reaches the projected-source
separation theorem through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives a projected-generator detector for every nonzero
concrete boundary-zero Kirchhoff chain through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives the projected-generator detector through the finite
collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives the projected-generator detector
through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives the projected-generator detector
through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives the projected-generator detector through the
height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives the projected-generator detector through the
finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives the projected-generator
detector through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives the projected-generator
detector through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives the projected-generator detector through the
height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives the projected-generator detector through the
finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives the projected-generator
detector through the height-ordered witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives the projected-generator
detector through the finite collar-layer witness surface. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives the pointwise orthogonality characterization against
the projected Definition 4.8 generator span through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Canonical source witness choice gives the pointwise orthogonality characterization through
the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives the pointwise orthogonality
characterization through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus canonical witness choice gives the pointwise orthogonality
characterization through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives the pointwise orthogonality characterization
through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- The local at-most-one source criterion gives the pointwise orthogonality characterization
through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives the pointwise
orthogonality characterization through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus the local at-most-one criterion gives the pointwise
orthogonality characterization through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives the pointwise orthogonality characterization
through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Same-boundary one-collar source geometry gives the pointwise orthogonality characterization
through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives the pointwise
orthogonality characterization through the height-ordered witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

/-- Successor-cycle source plus same-boundary one-collar geometry gives the pointwise
orthogonality characterization through the finite collar-layer witness surface. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry
        hG)
      C0 hC0 verticesOf

end Mettapedia.GraphTheory.FourColor
