import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceImpossibility

/-!
# Replacement positive geometric source packages for Theorem 4.9

The canonical-choice and source-preserving one-collar packages are structurally inconsistent with
the current purified selected-boundary carrier.  This file records the replacement positive
source surface: carry the already boundary-aware witness-cover data directly, together with
nonempty purified carrier on the same embedding.  These packages are deliberately downstream of
canonical witness choice, so they do not introduce the facewise at-most-one collapse proved in
`Theorem49PositiveGeometricSourceImpossibility`.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A nonempty carrier rules out adding closed-walk source data plus canonical witness choice on
the same embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, hchoice⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, hchoice, hCarrier⟩

/-- A nonempty carrier also rules out closed-walk source data plus source-preserving one-collar
geometry on the same embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_of_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
        collar.numCollars = 1 ∧
          collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData := by
  rintro ⟨source, collar, hnum, hboundary⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, collar, hnum, hboundary, hCarrier⟩

/-- Fixed-embedding replacement positive package using height-ordered witness-cover data. -/
def Theorem49HeightOrderedPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- If an embedding has no height-ordered witness-cover data at all, it cannot carry the
height-ordered replacement package. -/
theorem not_heightOrderedPositiveProjectedGeometryOn_of_not_nonempty_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hData : ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb)) :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rintro ⟨data, _hCarrier⟩
  exact hData ⟨data⟩

/-- The height-ordered replacement package gives the nonempty projected synthesis endpoint on the
same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49HeightOrderedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data C0 hC0 hCarrier

/-- The height-ordered replacement package gives the route-facing raw quotient/error conclusion
at the same embedding, by first reaching the nonempty projected synthesis endpoint. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_heightOrderedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49HeightOrderedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level replacement package using height-ordered witness-cover data and a nonempty
purified selected-boundary carrier on the same embedding. -/
structure Theorem49HeightOrderedPositiveProjectedGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49HeightOrderedPositiveProjectedGeometry

/-- Forget the graph-level height-ordered replacement package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49HeightOrderedPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.data, geom.carrier_nonempty⟩

/-- The graph-level height-ordered package is exactly existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- The height-ordered replacement package reaches the current nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- Graph-level height-ordered replacement package consuming the raw quotient/error endpoint on
its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_heightOrderedPositiveProjectedGeometryOn
      geom.on C0 hC0 hx

end Theorem49HeightOrderedPositiveProjectedGeometry

/-- Fixed-embedding replacement positive package using finite collar-layer witness-cover data. -/
def Theorem49CollarLayerPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- If an embedding has no collar-layer witness-cover data at all, it cannot carry the finite
collar-layer replacement package. -/
theorem not_collarLayerPositiveProjectedGeometryOn_of_not_nonempty_collarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hData : ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rintro ⟨data, _hCarrier⟩
  exact hData ⟨data⟩

/-- The finite collar-layer replacement package gives the nonempty projected synthesis endpoint
on the same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49CollarLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      data C0 hC0 hCarrier

/-- The finite collar-layer replacement package gives the route-facing raw quotient/error
conclusion at the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49CollarLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The height-ordered and finite collar-layer replacement packages are equivalent on a fixed
embedding.  The conversion from height to collars groups peeled faces by height; the reverse
conversion uses layer index as height. -/
theorem heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb ↔
      Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨data, hCarrier⟩
    exact
      ⟨planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData data,
        hCarrier⟩
  · rintro ⟨data, hCarrier⟩
    exact ⟨data.toHeightOrderedFacePeelWitnessData, hCarrier⟩

/-- A well-founded parent witness-cover package plus a local unblocked endpoint gives the
height-ordered replacement source by ranking parents with the canonical well-founded height. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The same well-founded parent witness-cover package also gives the finite-collar replacement
source by grouping the induced height-ordered data into collar layers. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint)

/-- A well-founded parent witness-cover package, a local unblocked endpoint, and a Tait coloring
reach the corrected nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint)
      C0 hC0

/-- A well-founded parent witness-cover package and a local unblocked endpoint also give the
route-facing raw quotient/error conclusion at the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- A well-founded parent witness-cover package plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier gives the height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- A well-founded parent witness-cover package plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier gives the finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- A well-founded parent witness-cover package, endpoint-support separation, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring reach the corrected nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- A well-founded parent witness-cover package plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier also give the route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data hEndpointDisjoint hRawCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Boundary-root interior-dual parent data is already a height-ordered replacement source once
the purified selected-boundary carrier is nonempty on the same embedding. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    ⟨planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
        data.toInteriorDualHeightParentPeelData,
      hCarrier⟩

/-- The same boundary-root interior-dual parent data also yields the finite-collar replacement
source by grouping the induced height data into collar layers. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
        data hCarrier)

/-- Boundary-root interior-dual parent data with a surviving purified carrier reaches the
corrected nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
        data hCarrier)
      C0 hC0

/-- Boundary-root interior-dual parent data with a surviving purified carrier also give the
route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData
      data hCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Boundary-root interior-dual parent data plus a local unblocked endpoint gives the
height-ordered replacement source without separately repackaging carrier nonemptiness. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Boundary-root interior-dual parent data plus a local unblocked endpoint gives the
finite-collar replacement source directly. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Boundary-root interior-dual parent data, a local unblocked endpoint, and a Tait coloring
reach the corrected nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Boundary-root interior-dual parent data and a local unblocked endpoint also give the
route-facing raw quotient/error conclusion directly. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Boundary-root interior-dual parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier gives the height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Boundary-root interior-dual parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier gives the finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Boundary-root interior-dual parent data, endpoint-support separation, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring reach the corrected nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Boundary-root interior-dual parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier also give the route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data hEndpointDisjoint hRawCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Two-sided annulus-root parent data is already a height-ordered replacement source once the
purified selected-boundary carrier is nonempty on the same embedding. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      data.interiorData hCarrier

/-- The same two-sided annulus-root parent data also yields the finite-collar replacement source
on the same embedding. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      data.interiorData hCarrier

/-- Two-sided annulus-root parent data plus a local unblocked endpoint gives the height-ordered
replacement source without separately repackaging carrier nonemptiness. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data.interiorData hEndpoint

/-- Two-sided annulus-root parent data plus a local unblocked endpoint gives the finite-collar
replacement source directly. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data.interiorData hEndpoint

/-- Two-sided annulus-root parent data, a local unblocked endpoint, and a Tait coloring reach
the corrected nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data.interiorData hEndpoint C0 hC0

/-- Two-sided annulus-root parent data and a local unblocked endpoint also give the route-facing
raw quotient/error conclusion directly. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Two-sided annulus-root parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier gives the height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data.interiorData hEndpointDisjoint hRawCarrier

/-- Two-sided annulus-root parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier gives the finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data.interiorData hEndpointDisjoint hRawCarrier

/-- Two-sided annulus-root parent data, endpoint-support separation, a nonempty raw interior-edge
endpoint carrier, and a Tait coloring reach the corrected nonempty projected theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data.interiorData hEndpointDisjoint hRawCarrier C0 hC0

/-- Two-sided annulus-root parent data plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier also give the route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data hEndpointDisjoint hRawCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- A BFS annulus construction is already a height-ordered replacement source once the purified
selected-boundary carrier is live on the same embedding. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData, hCarrier⟩

/-- A BFS annulus construction with a surviving purified carrier reaches the corrected nonempty
projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction
        data hCarrier)
      C0 hC0

/-- A BFS annulus construction with a surviving purified carrier also gives the route-facing raw
quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusConstruction
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction
      data hCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- A BFS annulus construction plus a local unblocked endpoint gives the height-ordered
replacement source without separately repackaging carrier nonemptiness. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- A BFS annulus construction, a local unblocked endpoint, and a Tait coloring reach the
corrected nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- A BFS annulus construction and a local unblocked endpoint also give the route-facing raw
quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The same annulus-construction hypotheses that feed the positive endpoint also expose a
terminal peeled face whose non-witness remainders already lie on the ambient annulus boundary. -/
theorem theorem49TerminalPeelFaceBoundaryRemainders_of_planarBoundaryAnnulusConstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  rcases
      (selectedBoundaryInteriorEdgeEndpointVertices_nonempty_iff_exists_unblocked_interior_endpoint
        emb).1 hCarrier with
    ⟨e, heInterior, _v, _hv, _hAvoid⟩
  exact data.exists_terminal_peelFace_boundary_remainders_of_mem_interiorEdgeSupport
    heInterior

/-- The local unblocked endpoint form of the terminal boundary-break diagnostic for an annulus
construction. -/
theorem theorem49TerminalPeelFaceBoundaryRemainders_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  exact
    theorem49TerminalPeelFaceBoundaryRemainders_of_planarBoundaryAnnulusConstruction
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- A geometry-facing annulus collar package, together with the purified nonempty carrier on the
same embedding, is already a fixed-embedding finite-collar replacement positive source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData, hCarrier⟩

/-- The same annulus collar package also gives the height-ordered replacement source by forgetting
the finite layer index to its induced height order. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData, hCarrier⟩

/-- Annulus collar geometry plus a local unblocked interior endpoint gives the finite-collar
replacement package without separately repackaging carrier nonemptiness. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Annulus collar geometry plus a local unblocked interior endpoint gives the height-ordered
replacement package directly. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Annulus collar geometry plus endpoint-support separation and a nonempty raw interior-edge
endpoint carrier gives the finite-collar replacement package directly. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Annulus collar geometry plus endpoint-support separation and a nonempty raw interior-edge
endpoint carrier gives the height-ordered replacement package directly. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- A geometry-facing annulus collar package, plus a surviving purified carrier and a Tait
coloring, reaches the corrected nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier)
      C0 hC0

/-- A geometry-facing annulus collar package and a surviving purified carrier also give the
route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
      data hCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Annulus collar geometry, a local unblocked endpoint, and a Tait coloring reach the corrected
nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Annulus collar geometry and a local unblocked endpoint also give the route-facing raw
quotient/error conclusion directly. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Annulus collar geometry plus endpoint-support separation, a nonempty raw interior-edge
endpoint carrier, and a Tait coloring reach the corrected nonempty projected theorem-4.9
synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Annulus collar geometry plus endpoint-support separation and a nonempty raw interior-edge
endpoint carrier also give the route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      data hEndpointDisjoint hRawCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level replacement package using finite collar-layer witness-cover data and a nonempty
purified selected-boundary carrier on the same embedding. -/
structure Theorem49CollarLayerPositiveProjectedGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  data : PlanarBoundaryCollarLayerFacePeelWitnessData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49CollarLayerPositiveProjectedGeometry

/-- Forget the graph-level finite collar-layer replacement package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49CollarLayerPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.data, geom.carrier_nonempty⟩

/-- The graph-level finite collar-layer package is exactly existence of the fixed-embedding
predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- The finite collar-layer replacement package reaches the current nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49CollarLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- Graph-level finite collar-layer replacement package consuming the raw quotient/error
endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49CollarLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_collarLayerPositiveProjectedGeometryOn
      geom.on C0 hC0 hx

/-- Finite collar-layer replacement data canonically yields the height-ordered replacement
package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49CollarLayerPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := geom.emb
  data := geom.data.toHeightOrderedFacePeelWitnessData
  carrier_nonempty := geom.carrier_nonempty

end Theorem49CollarLayerPositiveProjectedGeometry

namespace Theorem49HeightOrderedPositiveProjectedGeometry

/-- Height-ordered replacement data canonically yields the finite collar-layer replacement
package by grouping peeled faces according to height. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G where
  emb := geom.emb
  data := planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData
    geom.data
  carrier_nonempty := geom.carrier_nonempty

end Theorem49HeightOrderedPositiveProjectedGeometry

/-- Graph-level height-ordered replacement package obtained from well-founded parent witness data
and a local unblocked interior endpoint on the same embedding. -/
noncomputable def theorem49HeightOrderedPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := emb
  data := data.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty :=
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).1 hEndpoint

/-- Graph-level finite-collar replacement package obtained from well-founded parent witness data
and a local unblocked interior endpoint on the same embedding. -/
noncomputable def theorem49CollarLayerPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  (theorem49HeightOrderedPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    (G := G) (emb := emb) data hEndpoint).toCollarLayerPositiveProjectedGeometry

/-- Graph-level finite-collar replacement package obtained from annulus collar geometry and a
surviving purified carrier on the same embedding. -/
noncomputable def theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometry G where
  emb := emb
  data := data.toPlanarBoundaryCollarLayerFacePeelWitnessData
  carrier_nonempty := hCarrier

/-- Graph-level height-ordered replacement package obtained from annulus collar geometry and a
surviving purified carrier on the same embedding. -/
noncomputable def theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := emb
  data := data.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty := hCarrier

/-- Graph-level finite-collar replacement package obtained from annulus collar geometry and a
local unblocked interior endpoint on the same embedding. -/
noncomputable def theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    (G := G) data
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).1 hEndpoint)

/-- Graph-level height-ordered replacement package obtained from annulus collar geometry and a
local unblocked interior endpoint on the same embedding. -/
noncomputable def theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    (G := G) data
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).1 hEndpoint)

/-- Existential annulus collar geometry plus a surviving carrier is enough for the graph-level
finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential annulus collar geometry plus a surviving carrier is enough for the graph-level
height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential annulus collar geometry plus a local unblocked interior endpoint is enough for the
graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential annulus collar geometry plus a local unblocked interior endpoint is enough for the
graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential well-founded parent witness data plus a local unblocked endpoint is enough for
the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential well-founded parent witness data plus a local unblocked endpoint is enough for
the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential well-founded parent witness data plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier gives the graph-level height-ordered replacement source
package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential well-founded parent witness data plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier gives the graph-level finite-collar replacement source
package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential annulus collar geometry plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier is enough for the graph-level finite-collar replacement source
package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential annulus collar geometry plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier is enough for the graph-level height-ordered replacement source
package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential two-sided annulus-root parent data plus a surviving carrier is enough for the
graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData
      data hCarrier with
    ⟨collarData, hCarrier'⟩
  exact ⟨{ emb := emb, data := collarData, carrier_nonempty := hCarrier' }⟩

/-- Existential two-sided annulus-root parent data plus a surviving carrier is enough for the
graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData
      data hCarrier with
    ⟨heightData, hCarrier'⟩
  exact ⟨{ emb := emb, data := heightData, carrier_nonempty := hCarrier' }⟩

/-- Existential two-sided annulus-root parent data plus a local unblocked interior endpoint is
enough for the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data hEndpoint with
    ⟨collarData, hCarrier⟩
  exact ⟨{ emb := emb, data := collarData, carrier_nonempty := hCarrier }⟩

/-- Existential two-sided annulus-root parent data plus a local unblocked interior endpoint is
enough for the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpoint⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data hEndpoint with
    ⟨heightData, hCarrier⟩
  exact ⟨{ emb := emb, data := heightData, carrier_nonempty := hCarrier }⟩

/-- Existential two-sided annulus-root parent data plus endpoint-support separation and a
nonempty raw interior-edge endpoint carrier is enough for the graph-level finite-collar
replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential two-sided annulus-root parent data plus endpoint-support separation and a
nonempty raw interior-edge endpoint carrier is enough for the graph-level height-ordered
replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential two-sided annulus-root parent data plus a surviving carrier reaches the graph-
level nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
        data C0 hC0 hCarrier⟩

/-- Existential two-sided annulus-root parent data plus a surviving carrier and a Kirchhoff chain
on that same embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData
        data C0 hC0 hCarrier hx⟩

/-- Existential two-sided annulus-root parent data plus a local unblocked interior endpoint
reaches the graph-level nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait
coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0⟩

/-- Existential two-sided annulus-root parent data plus a local unblocked endpoint and a
Kirchhoff chain on that same embedding reach the graph-level raw theorem-4.9 quotient/error
endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0 hx⟩

/-- Existential two-sided annulus-root parent data plus endpoint-support separation and a
nonempty raw interior-edge endpoint carrier reaches the graph-level nonempty projected theorem-4.9
synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential two-sided annulus-root parent data plus endpoint-support separation, a nonempty
raw interior-edge endpoint carrier, and a Kirchhoff chain on that same embedding reach the
graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0 hx⟩

/-- Existential annulus collar geometry plus a surviving carrier reaches the graph-level
nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
        data hCarrier C0 hC0⟩

/-- Existential annulus collar geometry plus a surviving carrier and a Kirchhoff chain on that
same embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry
        data hCarrier C0 hC0 hx⟩

/-- Existential annulus collar geometry plus a local unblocked interior endpoint reaches the
graph-level nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0⟩

/-- Existential annulus collar geometry plus a local unblocked endpoint and a Kirchhoff chain on
that same embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0 hx⟩

/-- Existential well-founded parent witness data plus a local unblocked endpoint reaches the
graph-level nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0⟩

/-- Existential well-founded parent witness data plus a local unblocked endpoint and a Kirchhoff
chain on that same embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint C0 hC0 hx⟩

/-- Existential well-founded parent witness data plus endpoint-support separation and a nonempty
raw interior-edge endpoint carrier reaches the graph-level nonempty projected theorem-4.9
synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential well-founded parent witness data plus endpoint-support separation, a nonempty
raw interior-edge endpoint carrier, and a Kirchhoff chain on that same embedding reach the
graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0 hx⟩

/-- Existential annulus collar geometry plus endpoint-support separation and a nonempty raw
interior-edge endpoint carrier reaches the graph-level nonempty projected theorem-4.9 synthesis
endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential annulus collar geometry plus endpoint-support separation, a nonempty raw
interior-edge endpoint carrier, and a Kirchhoff chain on that same embedding reach the
graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hEndpointDisjoint, hRawCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        data hEndpointDisjoint hRawCarrier C0 hC0 hx⟩

/-- Annulus collar geometry plus peeled-face endpoint no-touch on its canonical construction and
a nonempty raw interior-edge endpoint carrier gives the finite-collar replacement package. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)

/-- Annulus collar geometry plus peeled-face endpoint no-touch on its canonical construction and
a nonempty raw interior-edge endpoint carrier gives the height-ordered replacement package. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)

/-- Annulus collar geometry, peeled-face endpoint no-touch on its canonical construction, a
nonempty raw interior-edge endpoint carrier, and a Tait coloring reach the corrected nonempty
projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)
      C0 hC0

/-- Annulus collar geometry plus peeled-face endpoint no-touch on its canonical construction and
a nonempty raw interior-edge endpoint carrier also give the route-facing raw quotient/error
conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
      data hPeelNoTouch hRawCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential annulus collar geometry plus peeled-face endpoint no-touch on its canonical
construction and a nonempty raw interior-edge endpoint carrier gives the graph-level finite-collar
replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)⟩

/-- Existential annulus collar geometry plus peeled-face endpoint no-touch on its canonical
construction and a nonempty raw interior-edge endpoint carrier gives the graph-level
height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)⟩

/-- Existential annulus collar geometry plus peeled-face endpoint no-touch on its canonical
construction and a nonempty raw interior-edge endpoint carrier reaches the graph-level nonempty
projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        data hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Existential annulus collar geometry plus peeled-face endpoint no-touch on its canonical
construction, a nonempty raw interior-edge endpoint carrier, and a Kirchhoff chain on that same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hPeelNoTouch, hRawCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        data hPeelNoTouch hRawCarrier C0 hC0 hx⟩

/-- Repaired previous-boundary witness geometry is a special annulus-collar source for the
finite-collar replacement package once the purified carrier survives. -/
noncomputable def theorem49CollarLayerPositiveProjectedGeometry_of_annulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    (G := G) data.toPlanarBoundaryAnnulusCollarGeometry hCarrier

/-- Repaired previous-boundary witness geometry is a special annulus-collar source for the
height-ordered replacement package once the purified carrier survives. -/
noncomputable def theorem49HeightOrderedPositiveProjectedGeometry_of_annulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    (G := G) data.toPlanarBoundaryAnnulusCollarGeometry hCarrier

/-- Repaired previous-boundary witness geometry reaches the corrected nonempty projected
theorem-4.9 synthesis endpoint through its underlying annulus collar geometry. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
      data.toPlanarBoundaryAnnulusCollarGeometry hCarrier C0 hC0

/-- Repaired previous-boundary witness geometry with a surviving purified carrier also gives the
route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry
      data hCarrier C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Repaired previous-boundary witness geometry plus a local unblocked endpoint gives the
fixed-embedding finite-collar replacement package. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data.toPlanarBoundaryAnnulusCollarGeometry hEndpoint

/-- Repaired previous-boundary witness geometry plus a local unblocked endpoint gives the
fixed-embedding height-ordered replacement package. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      data.toPlanarBoundaryAnnulusCollarGeometry hEndpoint

/-- Repaired previous-boundary witness geometry and a local unblocked endpoint reach the
corrected nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
        data hEndpoint)
      C0 hC0

/-- Repaired previous-boundary witness geometry and a local unblocked endpoint also give the
route-facing raw quotient/error conclusion. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential repaired previous-boundary witness geometry plus a surviving carrier gives the
graph-level finite-collar replacement package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_annulusPreviousBoundaryWitnessGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusPreviousBoundaryWitnessGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential repaired previous-boundary witness geometry plus a surviving carrier gives the
graph-level height-ordered replacement package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_annulusPreviousBoundaryWitnessGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusPreviousBoundaryWitnessGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential repaired previous-boundary witness geometry plus a surviving carrier reaches the
graph-level nonempty projected theorem-4.9 synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusPreviousBoundaryWitnessGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, data, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry
        data hCarrier C0 hC0⟩

/-- Existential repaired previous-boundary witness geometry plus a surviving carrier and a
Kirchhoff chain on that same embedding reach the graph-level raw theorem-4.9 quotient/error
endpoint. -/
theorem exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_annulusPreviousBoundaryWitnessGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, data, hCarrier, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_annulusPreviousBoundaryWitnessGeometry
        data hCarrier C0 hC0 hx⟩

end Mettapedia.GraphTheory.FourColor
