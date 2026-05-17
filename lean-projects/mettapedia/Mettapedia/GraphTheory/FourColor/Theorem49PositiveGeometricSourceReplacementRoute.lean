import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement

/-!
# Route-facing replacement positive geometric source packages for Theorem 4.9

The direct replacement surface in `Theorem49PositiveGeometricSourceReplacement` is formulated in
terms of annulus collar geometry plus a surviving purified selected-boundary carrier.  This file
connects that surface back to the honest closed-walk source shell and to the successor-cycle
boundary-order source shell used earlier in the route.  No one-collar or canonical-choice
condition is introduced here.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data,
same-embedding annulus collar geometry, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing positive closed-walk package cannot live in the facewise at-most-one
branch: its surviving purified carrier forces some face boundary to contain two distinct
interior edges.  The annulus collar data is retained in the package for the theorem-4.9 route,
but the obstruction itself only uses the honest closed-walk source and the live carrier. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk annulus-collar package is incompatible with the facewise
at-most-one interior-edge condition, since that condition forces the purified selected-boundary
interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- The route-facing closed-walk annulus package gives the fixed-embedding finite-collar
replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing closed-walk annulus package also gives the fixed-embedding height-ordered
replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing closed-walk annulus package reaches the current nonempty projected
synthesis endpoint through the direct annulus-collar bridge. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
      data hCarrier C0 hC0

/-- The route-facing closed-walk annulus package also reaches the route-facing raw Definition 4.8
quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The route-facing closed-walk annulus package already reaches the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, and a local unblocked endpoint
package the fixed-embedding route-facing replacement source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring reach the nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring already reach the full theorem-4.9 synthesis endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring also reach the route-facing raw Definition 4.8 quotient/error package for every
Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, and a local
unblocked endpoint package the fixed-embedding route-facing replacement source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data.toPlanarBoundaryAnnulusCollarGeometry hEndpoint

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly.  The source is retained in the statement for route traceability, while the
positive geometric burden is carried by the acyclic witness-cover data. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint
directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (_hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data.toPlanarBoundaryHeightOrderedFacePeelWitnessData C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly.  Once this shell and the live endpoint survive on the same embedding, no
additional replacement-side lowering is needed. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a local unblocked endpoint reaches the current nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a local unblocked endpoint already reach the full theorem-4.9 synthesis
endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint directly.  This is the positive
replacement source surface that avoids deriving root-distance interior-dual data. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain
on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring reach the nonempty
projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint
      (interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
        (G := G) (emb := emb) hInteriorCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring also reach the
route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain on the same
embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
      source data hEndpointDisjoint hInteriorCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier
reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint
through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data, the
selected-boundary-contact construction shell, and a nonempty purified selected-boundary
carrier. -/
def Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- Honest closed-walk source data, the selected-boundary-contact construction shell, and a
local unblocked endpoint package the fixed-embedding route-facing construction-shell replacement
source. -/
theorem theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The route-facing closed-walk selected-boundary-contact construction shell still cannot live
in the facewise at-most-one branch: its surviving purified carrier already forces some ambient
face boundary to contain two distinct interior edges. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell is incompatible
with the facewise at-most-one interior-edge condition, since that condition forces the purified
selected-boundary interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell gives the
fixed-embedding height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      data hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing closed-walk selected-boundary-contact construction shell reaches the
nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk selected-boundary-contact construction shell also reaches the
route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with the
same-embedding selected-boundary-contact construction shell and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Forget the graph-level closed-walk selected-boundary-contact construction package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.data, geom.carrier_nonempty⟩

/-- The graph-level closed-walk selected-boundary-contact construction package is exactly
existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk selected-boundary-contact construction data canonically yields the
graph-level height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := geom.emb
  data := geom.data.construction.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing closed-walk selected-boundary-contact construction data canonically yields the
graph-level finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toHeightOrderedPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing closed-walk selected-boundary-contact construction package reaches the
nonempty projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk selected-boundary-contact construction package also consumes
the raw quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing closed-walk selected-boundary-contact construction package already
carries witness ownership on the induced annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing closed-walk selected-boundary-contact construction package also reaches
the graph-level full theorem-4.9 synthesis endpoint once the induced annulus decomposition
carries witness ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding selected-boundary-contact
construction data and a surviving purified carrier package into the graph-level closed-walk
selected-boundary-contact replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding selected-boundary-contact
construction data and a local unblocked endpoint package into the graph-level closed-walk
selected-boundary-contact replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
the selected-boundary-contact construction shell, selected-boundary arcs, and a nonempty
purified selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle selected-boundary-contact construction package lowers to
the closed-walk selected-boundary-contact construction package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle selected-boundary-contact construction shell likewise
forces some ambient face boundary to contain two distinct interior edges, by lowering to the
corresponding honest closed-walk package on the same embedding. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell is likewise
incompatible with the facewise at-most-one interior-edge condition. -/
theorem not_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨_boundaryData, dartCycles, _data, _hselected, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Successor-cycle source data, the selected-boundary-contact construction shell,
selected-boundary arcs, and a local unblocked endpoint package the fixed-embedding route-facing
successor-cycle construction-shell replacement source. -/
theorem theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, data, hboundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The route-facing successor-cycle selected-boundary-contact construction shell gives the
fixed-embedding height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell reaches the
nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle selected-boundary-contact construction shell also reaches
the route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with the
same-embedding selected-boundary-contact construction shell and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb
  selectedBoundaryArc : ∀ f : AmbientFace emb.faces,
    (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
      |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle selected-boundary-contact construction package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.data, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle selected-boundary-contact construction package is exactly
existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          data := data,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle selected-boundary-contact construction package to
the honest closed-walk selected-boundary-contact construction shell. -/
noncomputable def toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G where
  emb := geom.emb
  source := PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc
  data := geom.data
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle selected-boundary-contact construction data canonically yields
the graph-level height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle selected-boundary-contact construction data canonically yields
the graph-level finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle selected-boundary-contact construction package reaches the
nonempty projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle selected-boundary-contact construction package also
consumes the raw quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing successor-cycle selected-boundary-contact construction package already
carries witness ownership on the induced annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing successor-cycle selected-boundary-contact construction package also reaches
the graph-level full theorem-4.9 synthesis endpoint once the induced annulus decomposition
carries witness ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Existential route-facing successor-cycle selected-boundary-contact construction data and a
surviving purified carrier package into the graph-level successor-cycle selected-boundary-contact
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential route-facing successor-cycle selected-boundary-contact construction data and a
local unblocked endpoint package into the graph-level successor-cycle selected-boundary-contact
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data, the
construction-side face-layer shell, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing closed-walk construction-face-layer package still cannot live in the
facewise at-most-one branch: its surviving purified carrier already forces some ambient face
boundary to contain two distinct interior edges. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk construction-face-layer package is incompatible with the
facewise at-most-one interior-edge condition, since that condition forces the purified selected-
boundary interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Honest closed-walk source data, the construction-side face-layer shell, and a local
unblocked endpoint package the fixed-embedding route-facing construction-shell replacement
source. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The stronger selected-boundary-contact construction shell lowers directly to the
route-facing closed-walk construction-face-layer package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data.toPlanarBoundaryAnnulusConstructionFaceLayerData hEndpoint

/-- The route-facing closed-walk construction-face-layer package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstructionFaceLayerData
      data hCarrier

/-- The route-facing closed-walk construction-face-layer package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing closed-walk construction-face-layer package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk construction-face-layer package also reaches the route-facing
raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with the
same-embedding construction-face-layer shell and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  data : PlanarBoundaryAnnulusConstructionFaceLayerData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Forget the graph-level closed-walk construction-face-layer package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.data, geom.carrier_nonempty⟩

/-- The graph-level closed-walk construction-face-layer package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk construction-face-layer data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := geom.emb
  data := geom.data.construction.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing closed-walk construction-face-layer data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toHeightOrderedPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing closed-walk construction-face-layer package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk construction-face-layer package also consumes the raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing closed-walk construction-face-layer package already carries witness
ownership on the resulting annulus decomposition, it reaches the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing closed-walk construction-face-layer package also reaches the graph-level
full theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding construction-face-layer data
and a surviving purified carrier package into the graph-level closed-walk
construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding construction-face-layer data
and a local unblocked endpoint package into the graph-level closed-walk
construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus the stronger selected-boundary-contact
construction shell and a local unblocked endpoint also package into the graph-level
closed-walk construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data.toPlanarBoundaryAnnulusConstructionFaceLayerData, hEndpoint⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
the construction-side face-layer shell, selected-boundary arcs, and a nonempty purified
selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle construction-face-layer package lowers to the closed-walk
construction-face-layer package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle construction-face-layer package likewise forces some
ambient face boundary to contain two distinct interior edges, by lowering to the corresponding
honest closed-walk package on the same embedding. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package is likewise incompatible
with the facewise at-most-one interior-edge condition. -/
theorem not_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨_boundaryData, dartCycles, _data, _hselected, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Successor-cycle source data, the construction-side face-layer shell, selected-boundary arcs,
and a local unblocked endpoint package the fixed-embedding route-facing successor-cycle
construction-shell replacement source. -/
theorem theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, data, hboundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The stronger selected-boundary-contact construction shell lowers directly to the
route-facing successor-cycle construction-face-layer package on the same embedding. -/
theorem theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc
      data.toPlanarBoundaryAnnulusConstructionFaceLayerData hEndpoint

/-- The route-facing successor-cycle construction-face-layer package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package reaches the nonempty
projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle construction-face-layer package also reaches the
route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with the
same-embedding construction-face-layer shell and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  data : PlanarBoundaryAnnulusConstructionFaceLayerData emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle construction-face-layer package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.data, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle construction-face-layer package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          data := data,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle construction-face-layer package to the honest
closed-walk source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
closed-walk construction-face-layer replacement package. -/
def toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  data := geom.data
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle construction-face-layer package reaches the nonempty
projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle construction-face-layer package also consumes the raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing successor-cycle construction-face-layer package already carries
witness ownership on the resulting annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.boundaryRootSynthesis
    C0 hC0 hwitness

/-- The route-facing successor-cycle construction-face-layer package also reaches the graph-level
full theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Existential successor-cycle construction-face-layer data with a surviving purified carrier
package into the graph-level successor-cycle construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle construction-face-layer data with a local unblocked endpoint
package into the graph-level successor-cycle construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential successor-cycle data plus the stronger selected-boundary-contact construction
shell and a local unblocked endpoint also package into the graph-level successor-cycle
construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hEndpoint⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, data.toPlanarBoundaryAnnulusConstructionFaceLayerData, dartCycles,
        hselected, hEndpoint⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data and a local unblocked endpoint reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data and a local unblocked endpoint already reach the full theorem-4.9 synthesis endpoint
directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0⟩

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint through the induced honest closed-walk
source. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier reaches the
current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier already
reach the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpointDisjoint,
    hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data,
well-founded parent witness-cover data, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- Honest closed-walk source data, well-founded parent witness-cover data, and a local
unblocked endpoint package the fixed-embedding route-facing well-founded replacement source. -/
theorem theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The route-facing closed-walk well-founded package gives the fixed-embedding height-ordered
replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The route-facing closed-walk well-founded package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The route-facing closed-walk well-founded package reaches the nonempty projected theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk well-founded package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The route-facing closed-walk well-founded package already reaches the full theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    by
      rcases geom with ⟨_source, data, _hCarrier⟩
      exact
        theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
          data.toPlanarBoundaryHeightOrderedFacePeelWitnessData C0 hC0

/-- Graph-level route-facing replacement package for honest closed-walk source data with
same-embedding well-founded parent witness-cover data and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry (G : SimpleGraph V)
    where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  data : PlanarBoundaryWellFoundedFacePeelWitnessData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry

/-- Forget the graph-level closed-walk well-founded package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.data, geom.carrier_nonempty⟩

/-- The graph-level closed-walk well-founded package is exactly existence of the fixed-embedding
predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk well-founded data canonically yields the graph-level height-ordered
replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    (G := G)
    (emb := geom.emb)
    geom.data
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      geom.emb).2 geom.carrier_nonempty)

/-- Route-facing closed-walk well-founded data canonically yields the graph-level finite-collar
replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    (G := G)
    (emb := geom.emb)
    geom.data
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      geom.emb).2 geom.carrier_nonempty)

/-- The route-facing closed-walk well-founded package reaches the nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk well-founded package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The graph-level closed-walk well-founded package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  theorem49BoundaryRootSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
    geom.on C0 hC0

/-- The graph-level closed-walk well-founded package also yields the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

end Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a surviving purified carrier packages into the graph-level closed-walk
well-founded replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a local unblocked endpoint packages into the graph-level closed-walk
well-founded replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier package into the graph-level closed-walk well-founded replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
well-founded parent witness-cover data, selected-boundary arcs, and a nonempty purified
selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle well-founded package lowers to the closed-walk well-founded
package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle well-founded package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle well-founded package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle well-founded package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle well-founded package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The route-facing successor-cycle well-founded package already reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusWellFoundedPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometryOn_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- Graph-level route-facing replacement package for successor-cycle source data with
same-embedding well-founded parent witness-cover data and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  data : PlanarBoundaryWellFoundedFacePeelWitnessData emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle well-founded package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.data, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle well-founded package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          data := data,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle well-founded package to the honest closed-walk
source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle well-founded data canonically yields the graph-level
closed-walk well-founded replacement package. -/
def toClosedWalkAnnulusWellFoundedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusWellFoundedPositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  data := geom.data
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle well-founded data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusWellFoundedPositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle well-founded data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusWellFoundedPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle well-founded package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle well-founded package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The graph-level successor-cycle well-founded package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  theorem49BoundaryRootSynthesis_of_successorCycleAnnulusWellFoundedPositiveProjectedGeometryOn
    geom.on C0 hC0

/-- The graph-level successor-cycle well-founded package also yields the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

end Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry

/-- Existential successor-cycle well-founded data with a surviving purified carrier packages into
the graph-level successor-cycle well-founded replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle well-founded data with a local unblocked endpoint packages into
the graph-level successor-cycle well-founded replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential successor-cycle well-founded data, endpoint-support separation, and a nonempty
raw interior-edge endpoint carrier package into the graph-level successor-cycle well-founded
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, data, dartCycles, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusWellFoundedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, data, dartCycles, hselected,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint.  This exposes the newly formalized annulus-parent route branch directly at the honest
source shell. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData C0 hC0
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint reaches the current nonempty projected theorem-4.9
synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source interiorData hEndpoint C0 hC0⟩

/-- Successor-cycle source data, generic boundary-root interior-dual parent data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hEndpoint C0 hC0

/-- Successor-cycle source data, generic boundary-root interior-dual parent data, a local
unblocked endpoint, and a Tait coloring reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc interiorData hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint reaches the current nonempty projected theorem-4.9
synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc interiorData hEndpoint C0 hC0⟩

/-- Honest closed-walk source data together with the stronger source-fixed raw canonical-parent
shared-edge cover package reaches the nonempty projected theorem-4.9 synthesis endpoint directly
through the existing generic parent-data route. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
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
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      source
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint C0 hC0

/-- The same source-fixed raw canonical-parent shared-edge cover package also reaches the
route-facing raw Definition 4.8 quotient/error endpoint through the generic parent-data route. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level direct theorem-4.9 endpoint from the stronger source-fixed raw canonical-parent
shared-edge cover package.  This is the generic-parent counterpart to the selector and residual
route wrappers. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
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
  rcases h with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint C0 hC0⟩

/-- Successor-cycle source data together with the stronger source-fixed raw canonical-parent
shared-edge cover package reaches the nonempty projected theorem-4.9 synthesis endpoint through
the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
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
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
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
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint C0 hC0

/-- Successor-cycle source data together with the source-fixed raw canonical-parent shared-edge
cover package also reaches the raw Definition 4.8 quotient/error endpoint through the generic
parent-data route. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
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
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source shell for the direct generic-parent theorem-4.9 route
from the stronger source-fixed raw canonical-parent shared-edge cover package. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
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
  rcases h with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint C0 hC0⟩

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint.  This is the endpoint-separation
strengthening of the parent route at the honest source shell. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  have hEq :
      selectedBoundaryInteriorEdgeEndpointVertices emb =
        interiorEdgeEndpointSupport emb :=
    (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
      emb).2 hEndpointDisjoint
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
    rcases hRawCarrier with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [hEq] using hv
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData C0 hC0 hCarrier

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain
on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring reach the nonempty
projected theorem-4.9 synthesis endpoint.  This is the edge-level carrier form of the parent
route strengthening. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint
      (interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
        (G := G) (emb := emb) hInteriorCarrier)
      C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring also reach the
route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain on the same
embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
      source interiorData hEndpointDisjoint hInteriorCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier
reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source interiorData hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Successor-cycle source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, generic boundary-root interior-dual parent data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles hboundaryArc interiorData hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier
reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc interiorData hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier gives the graph-level finite-collar replacement
source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, interiorData, hCarrier⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier with
    ⟨data, hCarrier'⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier' }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier gives the graph-level height-ordered replacement
source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, interiorData, hCarrier⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier with
    ⟨data, hCarrier'⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier' }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier reaches the graph-level nonempty projected theorem-4.9
synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, _source, interiorData, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData
        interiorData hCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint gives the graph-level finite-collar replacement source
package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, interiorData, hEndpoint⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      interiorData hEndpoint with
    ⟨data, hCarrier⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint gives the graph-level height-ordered replacement
source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, interiorData, hEndpoint⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      interiorData hEndpoint with
    ⟨data, hCarrier⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier gives
the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, interiorData,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier gives
the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, interiorData,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier gives the graph-level finite-collar replacement
source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, dartCycles, interiorData, _hboundaryArc, hCarrier⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier with
    ⟨data, hCarrier'⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier' }⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier gives the graph-level height-ordered replacement
source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, dartCycles, interiorData, _hboundaryArc, hCarrier⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier with
    ⟨data, hCarrier'⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier' }⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier reaches the graph-level nonempty projected theorem-4.9
synthesis endpoint for any supplied Tait coloring. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, _boundaryData, dartCycles, interiorData, _hboundaryArc, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData
        interiorData hCarrier C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint gives the graph-level finite-collar replacement source
package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, dartCycles, interiorData, _hboundaryArc, hEndpoint⟩
  rcases
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      interiorData hEndpoint with
    ⟨data, hCarrier⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint gives the graph-level height-ordered replacement
source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, dartCycles, interiorData, _hboundaryArc, hEndpoint⟩
  rcases
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      interiorData hEndpoint with
    ⟨data, hCarrier⟩
  exact ⟨{ emb := emb, data := data, carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier gives
the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, interiorData, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, interiorData, hboundaryArc,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier gives
the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, interiorData, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, interiorData, hboundaryArc,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data,
boundary-root interior-dual parent data, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The stronger source-fixed raw canonical-parent shared-edge cover package also lands on the
route-facing closed-walk annulus-parent positive geometry surface once a purified selected-boundary
carrier is available. -/
theorem theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
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
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb := by
  exact
    ⟨source,
      interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover,
      hCarrier⟩

/-- The same source-fixed raw canonical-parent shared-edge cover package reaches the route-facing
closed-walk annulus-parent positive geometry surface from the weaker local endpoint condition. -/
theorem theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
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
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- The route-facing closed-walk annulus-parent package gives the fixed-embedding finite-collar
replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, interiorData, hCarrier⟩
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier

/-- The route-facing closed-walk annulus-parent package also gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, interiorData, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData
      interiorData hCarrier

/-- The route-facing closed-walk annulus-parent package reaches the nonempty projected theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, interiorData, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData C0 hC0 hCarrier

/-- The route-facing closed-walk annulus-parent package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with
same-embedding boundary-root interior-dual parent data and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry (G : SimpleGraph V)
    where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry

/-- Forget the graph-level closed-walk annulus-parent package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.interiorData, geom.carrier_nonempty⟩

/-- The graph-level closed-walk annulus-parent package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, interiorData, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          interiorData := interiorData,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk annulus-parent data canonically yields the graph-level finite-collar
replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G := by
  classical
  let h :=
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom.on
  exact
    { emb := geom.emb
      data := Classical.choose h
      carrier_nonempty := Classical.choose_spec h }

/-- Route-facing closed-walk annulus-parent data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G := by
  classical
  let h :=
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom.on
  exact
    { emb := geom.emb
      data := Classical.choose h
      carrier_nonempty := Classical.choose_spec h }

/-- The route-facing closed-walk annulus-parent package reaches the nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk annulus-parent package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing closed-walk annulus-parent package also gives the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing closed-walk annulus-parent package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a surviving purified carrier packages into the graph-level closed-walk
annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := interiorData,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data and a local unblocked endpoint packages into the graph-level closed-walk
annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := interiorData,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
parent data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier
packages into the graph-level closed-walk annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, interiorData,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Source-fixed raw canonical-parent shared-edge cover data plus a surviving purified carrier
packages into the graph-level closed-walk annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
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
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hCarrier⟩
  exact
    ⟨{ emb := emb
        , source := source
        , interiorData :=
          interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
            source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        , carrier_nonempty := hCarrier }⟩

/-- Source-fixed raw canonical-parent shared-edge cover data plus a local unblocked endpoint
packages into the graph-level closed-walk annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
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
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hEndpoint⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint⟩

/-- Source-fixed raw canonical-parent shared-edge cover data, endpoint-support separation, and a
nonempty raw interior-edge endpoint carrier package into the graph-level closed-walk
annulus-parent replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
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
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
      hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
boundary-root interior-dual parent data, selected-boundary arcs, and a nonempty purified
selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The stronger successor-cycle raw canonical-parent shared-edge cover package also lands on the
route-facing successor-cycle annulus-parent positive geometry surface once a purified
selected-boundary carrier is available. -/
theorem theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
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
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    ⟨boundaryData, dartCycles,
      interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover,
      hboundaryArc, hCarrier⟩

/-- The same successor-cycle raw canonical-parent shared-edge cover package reaches the
route-facing successor-cycle annulus-parent positive geometry surface from the weaker local
endpoint condition. -/
theorem theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
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
    Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- The route-facing successor-cycle annulus-parent package lowers to the closed-walk
annulus-parent package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      interiorData, hCarrier⟩

/-- The route-facing successor-cycle annulus-parent package gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle annulus-parent package also gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle annulus-parent package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle annulus-parent package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with
same-embedding boundary-root interior-dual parent data and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle annulus-parent package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.interiorData, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle annulus-parent package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          interiorData := interiorData,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle annulus-parent package to the honest closed-walk
source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle annulus-parent data canonically yields the graph-level
closed-walk annulus-parent replacement package. -/
def toClosedWalkAnnulusRootParentPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  interiorData := geom.interiorData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle annulus-parent data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G := by
  classical
  let h :=
    theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom.on
  exact
    { emb := geom.emb
      data := Classical.choose h
      carrier_nonempty := Classical.choose_spec h }

/-- Route-facing successor-cycle annulus-parent data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G := by
  classical
  let h :=
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom.on
  exact
    { emb := geom.emb
      data := Classical.choose h
      carrier_nonempty := Classical.choose_spec h }

/-- The route-facing successor-cycle annulus-parent package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle annulus-parent package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing successor-cycle annulus-parent package also gives the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing successor-cycle annulus-parent package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry

/-- Existential successor-cycle annulus-parent data with a surviving purified carrier packages
into the graph-level successor-cycle annulus-parent replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := interiorData,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle annulus-parent data with a local unblocked endpoint packages into
the graph-level successor-cycle annulus-parent replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, interiorData, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := interiorData,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential successor-cycle annulus-parent data, endpoint-support separation, and a nonempty
raw interior-edge endpoint carrier package into the graph-level successor-cycle annulus-parent
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, interiorData, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, interiorData, hselected,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Successor-cycle raw canonical-parent shared-edge cover data plus a surviving purified carrier
packages into the graph-level successor-cycle annulus-parent replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
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
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hCarrier⟩
  exact
    ⟨{ emb := emb
        , boundaryData := boundaryData
        , dartCycles := dartCycles
        , interiorData :=
          interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc)
            peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        , selectedBoundaryArc := hboundaryArc
        , carrier_nonempty := hCarrier }⟩

/-- Successor-cycle raw canonical-parent shared-edge cover data plus a local unblocked endpoint
packages into the graph-level successor-cycle annulus-parent replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
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
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
        hpeelInterior, hcover,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint⟩

/-- Successor-cycle raw canonical-parent shared-edge cover data, endpoint-support separation, and
a nonempty raw interior-edge endpoint carrier package into the graph-level successor-cycle
annulus-parent replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
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
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
        hpeelInterior, hcover,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint.  The root-distance annulus construction supplies the acyclic parent
witness-cover datum consumed by the direct positive route. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source
      (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
        source interiorData)
      hEndpoint C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
a local unblocked endpoint, and a Tait coloring reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data and a local unblocked endpoint reaches the current nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source interiorData hEndpoint C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data, a local unblocked endpoint, and a Kirchhoff chain on that embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint directly. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with ⟨emb, source, interiorData, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source interiorData hEndpoint C0 hC0 hx⟩

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data, a
local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hEndpoint C0 hC0

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data, a
local unblocked endpoint, and a Tait coloring reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc interiorData hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
adjacency-distance data and a local unblocked endpoint reaches the current nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc interiorData hEndpoint C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
adjacency-distance data, a local unblocked endpoint, and a Kirchhoff chain on that embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint directly. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  rcases h with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc interiorData hEndpoint C0 hC0 hx⟩

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint.  This discharges the named local
endpoint witness at the root-distance source layer. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain
on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring reach the nonempty
projected theorem-4.9 synthesis endpoint.  This is the edge-level carrier form of the
root-distance source bridge: the raw endpoint carrier is derived from an actual interior edge. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint
      (interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
        (G := G) (emb := emb) hInteriorCarrier)
      C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring also reach the
route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain on the same
embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
      source interiorData hEndpointDisjoint hInteriorCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source interiorData hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the root-distance annulus construction, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source.boundaryReachability interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let construction :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source.boundaryReachability interiorData
  have hPeelNoTouch' : ∀ f ∈ construction.peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
    simpa [construction] using hPeelNoTouch
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData
      (PlanarBoundaryAnnulusConstruction.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        construction hPeelNoTouch' hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the root-distance annulus construction, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring also reach the route-facing raw Definition
4.8 quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source.boundaryReachability interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
      source interiorData hPeelNoTouch hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the root-distance annulus construction, a nonempty interior
edge, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source.boundaryReachability interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
      source interiorData hPeelNoTouch
      (interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
        (G := G) (emb := emb) hInteriorCarrier)
      C0 hC0

/-- Honest closed-walk source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the root-distance annulus construction, a nonempty interior
edge, and a Tait coloring also reach the route-facing raw Definition 4.8 quotient/error package
for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source.boundaryReachability interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeSupport
      source interiorData hPeelNoTouch hInteriorCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data, root-distance peeled-face endpoint no-touch, and a nonempty raw
interior-edge endpoint carrier reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_with_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
            source.boundaryReachability interiorData).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, interiorData, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
        source interiorData hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source interiorData hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles hboundaryArc interiorData hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
adjacency-distance data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc interiorData hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the induced root-distance annulus construction, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
      source interiorData
      (by
        simpa [source] using hPeelNoTouch)
      hRawCarrier C0 hC0

/-- Successor-cycle source data, generic boundary-root interior-dual adjacency-distance data,
peeled-face endpoint no-touch on the induced root-distance annulus construction, a nonempty raw
interior-edge endpoint carrier, and a Tait coloring also reach the route-facing raw Definition
4.8 quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
      boundaryData dartCycles hboundaryArc interiorData hPeelNoTouch hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding boundary-root interior-dual
adjacency-distance data, root-distance peeled-face endpoint no-touch, and a nonempty raw
interior-edge endpoint carrier reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_with_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
            boundaryData interiorData).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootDistance_peelFaces_endpoint_disjoint_selectedBoundarySupport
        boundaryData dartCycles hboundaryArc interiorData hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data,
boundary-root interior-dual adjacency-distance data, and a nonempty purified selected-boundary
carrier. -/
def Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing closed-walk annulus root-distance package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨source, interiorData, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
        source interiorData)
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The route-facing closed-walk annulus root-distance package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The route-facing closed-walk annulus root-distance package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, interiorData, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk annulus root-distance package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with
same-embedding boundary-root interior-dual adjacency-distance data and a surviving purified
carrier. -/
structure Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry

/-- Forget the graph-level closed-walk annulus root-distance package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.interiorData, geom.carrier_nonempty⟩

/-- The graph-level closed-walk annulus root-distance package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, interiorData, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          interiorData := interiorData,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk annulus root-distance data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    (G := G)
    (emb := geom.emb)
    (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      geom.source geom.interiorData)
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      geom.emb).2 geom.carrier_nonempty)

/-- Route-facing closed-walk annulus root-distance data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    (G := G)
    (emb := geom.emb)
    (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      geom.source geom.interiorData)
    ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      geom.emb).2 geom.carrier_nonempty)

/-- The route-facing closed-walk annulus root-distance package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk annulus root-distance package already reaches the full
theorem-4.9 synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing closed-walk annulus root-distance package also gives the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing closed-walk annulus root-distance package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data and a surviving purified carrier packages into the graph-level
closed-walk annulus root-distance replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := interiorData,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data and a local unblocked endpoint packages into the graph-level
closed-walk annulus root-distance replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := interiorData,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus same-embedding boundary-root interior-dual
adjacency-distance data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier package into the graph-level closed-walk annulus root-distance replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, interiorData,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
boundary-root interior-dual adjacency-distance data, selected-boundary arcs, and a nonempty
purified selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle annulus root-distance package lowers to the closed-walk
annulus root-distance package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      interiorData, hCarrier⟩

/-- The route-facing successor-cycle annulus root-distance package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle annulus root-distance package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle annulus root-distance package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle annulus root-distance package also reaches the route-facing
raw Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with
same-embedding boundary-root interior-dual adjacency-distance data and a surviving purified
carrier. -/
structure Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry

/-- Forget the graph-level successor-cycle annulus root-distance package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.interiorData, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle annulus root-distance package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          interiorData := interiorData,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle annulus root-distance package to the honest
closed-walk source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle annulus root-distance data canonically yields the graph-level
closed-walk annulus root-distance replacement package. -/
def toClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  interiorData := geom.interiorData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle annulus root-distance data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle annulus root-distance data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle annulus root-distance package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle annulus root-distance package already reaches the full
theorem-4.9 synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing successor-cycle annulus root-distance package also gives the graph-level
full theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing successor-cycle annulus root-distance package also consumes the route-facing
raw quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry

/-- Existential successor-cycle annulus root-distance data with a surviving purified carrier
packages into the graph-level successor-cycle annulus root-distance replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, interiorData, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := interiorData,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle annulus root-distance data with a local unblocked endpoint
packages into the graph-level successor-cycle annulus root-distance replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, interiorData, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := interiorData,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential successor-cycle annulus root-distance data, endpoint-support separation, and a
nonempty raw interior-edge endpoint carrier package into the graph-level successor-cycle annulus
root-distance replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, interiorData, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, interiorData, hselected,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
surviving carrier reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        ⟨source, data, hCarrier⟩ C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
local unblocked interior endpoint reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
surviving carrier already reach the full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        ⟨source, data, hCarrier⟩ C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
local unblocked interior endpoint already reach the full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Honest closed-walk source data, annulus collar geometry, endpoint-support separation, a
nonempty raw interior-edge endpoint carrier, and a Tait coloring reach the nonempty projected
theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, endpoint-support separation, a
nonempty raw interior-edge endpoint carrier, and a Tait coloring already reach the full
theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, endpoint-support separation, a
nonempty raw interior-edge endpoint carrier, and a Tait coloring also reach the route-facing raw
Definition 4.8 quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, annulus collar geometry, endpoint-support separation, and a
nonempty raw interior-edge endpoint carrier package the fixed-embedding route-facing replacement
source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
endpoint-support separation, and a nonempty raw interior-edge endpoint carrier reaches the current
nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
endpoint-support separation, and a nonempty raw interior-edge endpoint carrier already reach the
full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Honest closed-walk source data, annulus collar geometry, peeled-face endpoint no-touch on the
canonical collar construction, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
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
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, peeled-face endpoint no-touch on the
canonical collar construction, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, peeled-face endpoint no-touch on the
canonical collar construction, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain
on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
      source data hPeelNoTouch hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, annulus collar geometry, peeled-face endpoint no-touch on the
canonical collar construction, and a nonempty raw interior-edge endpoint carrier package the
fixed-embedding route-facing replacement source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        source data hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier already reach the full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        source data hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Graph-level route-facing replacement package for honest closed-walk source data with
same-embedding annulus collar geometry and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  collar : PlanarBoundaryAnnulusCollarGeometry emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry

/-- Forget the graph-level closed-walk annulus package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.collar, geom.carrier_nonempty⟩

/-- The graph-level closed-walk annulus package is exactly existence of the fixed-embedding
predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, collar, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          collar := collar,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk annulus data canonically yields the graph-level finite-collar
replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    geom.collar geom.carrier_nonempty

/-- Route-facing closed-walk annulus data canonically yields the graph-level height-ordered
replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    geom.collar geom.carrier_nonempty

/-- The route-facing closed-walk annulus package reaches the nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk annulus package already reaches the full theorem-4.9 synthesis
endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing closed-walk annulus package also gives the graph-level full theorem-4.9
synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing closed-walk annulus package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
surviving carrier packages into the graph-level closed-walk replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        collar := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
local unblocked endpoint packages into the graph-level closed-walk replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        collar := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
endpoint-support separation, and a nonempty raw interior-edge endpoint carrier packages into the
graph-level closed-walk replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier packages into the graph-level closed-walk replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
surviving carrier gives the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, data, hCarrier⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
local unblocked endpoint gives the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, data, hEndpoint⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier gives the graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
surviving carrier gives the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, data, hCarrier⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry and a
local unblocked endpoint gives the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _source, data, hEndpoint⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential honest closed-walk source data plus same-embedding annulus collar geometry,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier gives the graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
same-embedding annulus collar geometry, and a nonempty purified selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle annulus package still lowers to an honest closed-walk
annulus-boundary source on the same embedding. -/
theorem exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The successor-cycle annulus package lowers to the closed-walk route-facing replacement
package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle annulus-collar package also forces some ambient face
boundary to carry two distinct interior edges, by lowering to the corresponding honest
closed-walk package on the same embedding. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle annulus-collar package is likewise incompatible with the
facewise at-most-one interior-edge condition. -/
theorem not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨_boundaryData, dartCycles, _data, _hselected, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- The route-facing successor-cycle annulus package gives the fixed-embedding finite-collar
replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_boundaryData, _dartCycles, data, _hselected, hCarrier⟩
  exact theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing successor-cycle annulus package also gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_boundaryData, _dartCycles, data, _hselected, hCarrier⟩
  exact theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing successor-cycle annulus package reaches the current nonempty projected
synthesis endpoint through the replacement source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle annulus package also reaches the route-facing raw
Definition 4.8 quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The route-facing successor-cycle annulus package already reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
and a local unblocked endpoint package the fixed-embedding route-facing replacement source. -/
theorem theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, data, hselected,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles data hselected hEndpoint)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
a local unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles data hselected hEndpoint)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
a local unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential route-facing successor-cycle annulus data reaches the current nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩ C0 hC0⟩

/-- Existential route-facing successor-cycle annulus data with a local unblocked endpoint reaches
the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles data hselected hEndpoint C0 hC0⟩

/-- Existential route-facing successor-cycle annulus data already reach the full theorem-4.9
synthesis endpoint once the same embedding has a surviving carrier. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩ C0 hC0⟩

/-- Existential route-facing successor-cycle annulus data with a local unblocked endpoint already
reach the full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles data hselected hEndpoint C0 hC0⟩

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles data hselected hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
endpoint-support separation, and a nonempty raw interior-edge endpoint carrier package the
fixed-embedding route-facing replacement source. -/
theorem theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Existential route-facing successor-cycle annulus data with endpoint-support separation and a
nonempty raw interior-edge endpoint carrier reaches the current nonempty projected theorem-4.9
synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles data hselected hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential route-facing successor-cycle annulus data with endpoint-support separation and a
nonempty raw interior-edge endpoint carrier already reach the full theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles data hselected hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
peeled-face endpoint no-touch on the canonical collar construction, a nonempty raw interior-edge
endpoint carrier, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis endpoint
directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
peeled-face endpoint no-touch on the canonical collar construction, a nonempty raw interior-edge
endpoint carrier, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint
directly. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)
      C0 hC0

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
peeled-face endpoint no-touch on the canonical collar construction, a nonempty raw interior-edge
endpoint carrier, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
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
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles data hselected hPeelNoTouch hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle boundary-order source data, annulus collar geometry, selected-boundary arcs,
peeled-face endpoint no-touch on the canonical collar construction, and a nonempty raw
interior-edge endpoint carrier package the fixed-embedding route-facing replacement source. -/
theorem theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hselected : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles data hselected
      (data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        hPeelNoTouch hRawCarrier)

/-- Existential route-facing successor-cycle annulus data with peeled-face endpoint no-touch on
the canonical collar construction and a nonempty raw interior-edge endpoint carrier reaches the
current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles data hselected hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Existential route-facing successor-cycle annulus data with peeled-face endpoint no-touch on
the canonical collar construction and a nonempty raw interior-edge endpoint carrier already reach
the full theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hPeelNoTouch, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles data hselected hPeelNoTouch hRawCarrier C0 hC0⟩

/-- Graph-level route-facing replacement package for successor-cycle source data with
same-embedding annulus collar geometry and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  collar : PlanarBoundaryAnnulusCollarGeometry emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry

/-- Forget the graph-level route-facing annulus package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.collar, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level route-facing annulus package is exactly existence of the fixed-embedding
predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, collar, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          collar := collar,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle package to the honest closed-walk source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle annulus data canonically yields the graph-level closed-walk
annulus replacement package. -/
noncomputable def toClosedWalkAnnulusCollarPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  collar := geom.collar
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle annulus data canonically yields the graph-level finite-collar
replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    geom.collar geom.carrier_nonempty

/-- Route-facing successor-cycle annulus data canonically yields the graph-level height-ordered
replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    geom.collar geom.carrier_nonempty

/-- The route-facing successor-cycle annulus package reaches the nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  Theorem49CollarLayerPositiveProjectedGeometry.exists_nonemptyProjectedSynthesis
    geom.toCollarLayerPositiveProjectedGeometry C0 hC0

/-- The route-facing successor-cycle annulus package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toCollarLayerPositiveProjectedGeometry.boundaryRootSynthesis C0 hC0

/-- The route-facing successor-cycle annulus package also gives the graph-level full theorem-4.9
synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

/-- The route-facing successor-cycle annulus package also consumes the route-facing raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry

/-- Existential route-facing successor-cycle annulus data packages into the graph-level
successor-cycle replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        collar := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential route-facing successor-cycle annulus data with a local unblocked endpoint packages
into the graph-level successor-cycle replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        collar := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential route-facing successor-cycle annulus data with endpoint-support separation and a
nonempty raw interior-edge endpoint carrier packages into the graph-level successor-cycle
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hEndpointDisjoint, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, data, hselected,
        hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
          hEndpointDisjoint hRawCarrier⟩

/-- Existential route-facing successor-cycle annulus data with peeled-face endpoint no-touch on
the canonical collar construction and a nonempty raw interior-edge endpoint carrier packages into
the graph-level successor-cycle replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, data, hselected,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

/-- Existential route-facing successor-cycle annulus data gives the graph-level finite-collar
replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, _dartCycles, data, _hselected, hCarrier⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential route-facing successor-cycle annulus data with a local unblocked endpoint gives the
graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, _dartCycles, data, _hselected, hEndpoint⟩
  exact
    ⟨theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential route-facing successor-cycle annulus data with peeled-face endpoint no-touch on
the canonical collar construction and a nonempty raw interior-edge endpoint carrier gives the
graph-level finite-collar replacement source package. -/
theorem nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49CollarLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, data, hselected,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

/-- Existential route-facing successor-cycle annulus data gives the graph-level height-ordered
replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, _dartCycles, data, _hselected, hCarrier⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
      (G := G) (emb := emb) data hCarrier⟩

/-- Existential route-facing successor-cycle annulus data with a local unblocked endpoint gives the
graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, _boundaryData, _dartCycles, data, _hselected, hEndpoint⟩
  exact
    ⟨theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      (G := G) (emb := emb) data hEndpoint⟩

/-- Existential route-facing successor-cycle annulus data with peeled-face endpoint no-touch on
the canonical collar construction and a nonempty raw interior-edge endpoint carrier gives the
graph-level height-ordered replacement source package. -/
theorem nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f ∈ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
            (interiorEdgeEndpointSupport emb).Nonempty) :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, data, hselected, hPeelNoTouch, hRawCarrier⟩
  exact
    nonempty_theorem49HeightOrderedPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, data, hselected,
        data.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
          hPeelNoTouch hRawCarrier⟩

end Mettapedia.GraphTheory.FourColor
