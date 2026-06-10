import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

/-!
# Replacement positive source regression tests for Theorem 4.9

The direct replacement packages are the current positive target, but the existing honest
shared-interior-pair annulus model shows that boundary-order data, a Tait coloring, and a
nonempty purified carrier still do not automatically build either direct witness-cover package
on the same embedding.  The same obstruction also blocks the route-facing closed-walk and
successor-cycle annulus-collar packages, since those packages lower to the direct finite-collar
replacement predicate.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49PositiveGeometricSourceReplacementRegression

/-- The shared-interior-pair embedding has no height-ordered replacement geometry. -/
theorem not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding := by
  exact
    not_heightOrderedPositiveProjectedGeometryOn_of_not_nonempty_heightOrderedFacePeelWitnessData
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair

/-- The shared-interior-pair embedding has no finite collar-layer replacement geometry. -/
theorem not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding := by
  exact
    not_collarLayerPositiveProjectedGeometryOn_of_not_nonempty_collarLayerFacePeelWitnessData
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair

/-- The shared-interior-pair embedding has no route-facing closed-walk annulus-collar package. -/
theorem not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair :
    ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
      sharedInteriorPairAnnulusEmbedding := by
  intro geom
  exact
    not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- The shared-interior-pair embedding has no route-facing successor-cycle annulus-collar
package. -/
theorem not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair :
    ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
      sharedInteriorPairAnnulusEmbedding := by
  intro geom
  exact
    not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- A Tait coloring plus nonempty purified carrier is not enough to produce either replacement
geometry on the same shared-interior-pair embedding. -/
theorem sharedInteriorPair_tait_nonempty_carrier_without_replacementPositiveProjectedGeometryOn :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairAnnulusEmbedding).Nonempty ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨sharedInteriorPairTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The same shared-interior-pair witness also blocks the route-facing closed-walk and
successor-cycle annulus-collar packages. -/
theorem sharedInteriorPair_tait_nonempty_carrier_without_routeFacingAnnulusCollarPositiveProjectedGeometryOn :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairAnnulusEmbedding).Nonempty ∧
      ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨sharedInteriorPairTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Combined fixed-embedding calibration: the shared-interior-pair model has the coloring and
nonempty purified carrier but none of the direct or route-facing replacement packages. -/
theorem sharedInteriorPair_tait_nonempty_carrier_without_any_replacementPositiveProjectedGeometryOn :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairAnnulusEmbedding).Nonempty ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨sharedInteriorPairTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The shared-interior-pair carrier is witnessed by an explicit unblocked interior endpoint. -/
theorem hasUnblockedInteriorEndpoint_sharedInteriorPair :
    HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding := by
  exact
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      sharedInteriorPairAnnulusEmbedding).2
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair

/-- Even the first-order endpoint witness, together with a Tait coloring, is not enough to
produce any current replacement positive package on the shared-interior-pair embedding. -/
theorem sharedInteriorPair_tait_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The honest boundary-order shared-interior-pair model carries selected boundary arcs, a Tait
coloring, and nonempty purified carrier, while still failing both direct replacement packages on
that same embedding. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The same honest boundary-order witness fails the newer route-facing annulus-collar packages
on the same embedding. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_routeFacingAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Full witness package: boundary reachability, successor-cycle selected arcs, Tait coloring,
and nonempty purified carrier coexist with failure of every current replacement positive package
on the shared-interior-pair embedding. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Strengthened full witness package: boundary reachability, successor-cycle selected arcs, Tait
coloring, and an explicit unblocked interior endpoint coexist with failure of every current
replacement positive package on the shared-interior-pair embedding. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The exact one-collar current-boundary shell still does not rescue the boundary-order
replacement-positive route: the shared-interior-pair witness carries selected arcs, exact
one-collar current-boundary data, a Tait coloring, and an explicit unblocked endpoint, while
failing every current replacement positive package on the same embedding. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Consequently, boundary reachability, successor-cycle selected arcs, a Tait coloring, and a
nonempty purified carrier do not universally force either direct replacement package. -/
theorem not_forall_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
              Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair
  rcases hAny with hHeight | hCollar
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar

/-- The same data do not universally force the closed-walk annulus-collar source package. -/
theorem not_forall_closedWalkAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair)

/-- Nor do those data universally force the successor-cycle annulus-collar source package. -/
theorem not_forall_successorCycleAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair)

/-- Boundary reachability, successor-cycle selected arcs, a Tait coloring, and nonempty purified
carrier do not force either route-facing annulus-collar package. -/
theorem not_forall_routeFacingAnnulusCollarPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
              Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair
  rcases hAny with hClosedWalk | hSuccessorCycle
  · exact
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
        hClosedWalk
  · exact
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
        hSuccessorCycle

/-- The strengthened endpoint-witness form of the same obstruction: boundary reachability,
successor-cycle selected arcs, a Tait coloring, and an explicit unblocked interior endpoint do not
universally force any of the current direct or route-facing replacement packages. -/
theorem not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
              Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                  Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Even after adding exact one-collar current-boundary data, a Tait coloring, and an explicit
unblocked endpoint, the boundary-order source shell still does not universally force any current
replacement positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
              Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                  Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Exact one-collar current-boundary data does not rescue the successor-cycle endpoint-witness
obstruction: the same benchmark still carries a Tait coloring and an explicit unblocked interior
endpoint while missing even the raw height-ordered and collar-layer witness-cover data. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_witnessCoverData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      (by
        let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            sharedInteriorPairAnnulusBoundaryReachabilityData
            sharedInteriorPairDartSuccessorCycleGeometry
            sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using
            exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source),
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

/-- The named endpoint witness still does not upgrade the exact one-collar current-boundary
successor-cycle shell into even the raw height-ordered or collar-layer witness-cover data. -/
theorem
    not_forall_some_witnessCoverData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      (by
        let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            sharedInteriorPairAnnulusBoundaryReachabilityData
            sharedInteriorPairDartSuccessorCycleGeometry
            sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using
            exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

/-- Exact one-collar current-boundary data does not rescue the successor-cycle endpoint-witness
obstruction: the same benchmark still carries a Tait coloring and an explicit unblocked interior
endpoint while missing every current sufficient same-embedding geometric endpoint. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      (by
        let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            sharedInteriorPairAnnulusBoundaryReachabilityData
            sharedInteriorPairDartSuccessorCycleGeometry
            sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using
            exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source),
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- The named endpoint witness still does not upgrade the exact one-collar current-boundary
successor-cycle shell into any current sufficient same-embedding geometric endpoint. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  exact
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair
      (by
        intro emb boundaryData dartCycles hsel hcurrent hcolor hnonempty
        exact
          h emb boundaryData dartCycles hsel hcurrent hcolor
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty))

/-- The same obstruction stated at the honest closed-walk source layer: even a closed-walk
annulus boundary source, a Tait coloring, and an explicit unblocked endpoint do not force any
current direct or route-facing replacement package on the shared-interior-pair embedding. -/
theorem sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding ∧
      ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
        sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The honest closed-walk source shell remains obstructed even after adding exact one-collar
current-boundary data, a Tait coloring, and an explicit unblocked endpoint. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The same honest closed-walk source, coloring, and endpoint witness still do not produce
the raw height-ordered or collar-layer witness-cover data used by the direct replacement
packages. -/
theorem sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_witnessCoverData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

/-- The same source, coloring, and endpoint data still miss every current same-embedding
geometric endpoint that is known to be sufficient for the Theorem 4.9 synthesis layer. -/
theorem sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (BoundaryRootedFacePeelCertificate sharedInteriorPairAnnulusEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)) ∧
      ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data does not rescue the honest-source endpoint-witness
obstruction either: the same benchmark still carries a Tait coloring and an explicit unblocked
interior endpoint while missing even the raw height-ordered and collar-layer witness-cover data. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_witnessCoverData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

/-- The named endpoint witness still does not upgrade the exact one-collar current-boundary
honest-source shell into even the raw height-ordered or collar-layer witness-cover data. -/
theorem
    not_forall_some_witnessCoverData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

/-- Exact one-collar current-boundary data does not rescue the honest-source endpoint-witness
obstruction either: the same benchmark still carries a Tait coloring and an explicit unblocked
interior endpoint while missing every current sufficient same-embedding geometric endpoint. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Existential closed-walk-source obstruction: the shared-interior-pair graph has an embedding
with honest closed-walk annulus source data, a Tait coloring, and an unblocked endpoint, while
still failing every current direct or route-facing replacement package. -/
theorem exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          HasUnblockedInteriorEndpoint emb ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force any current direct or route-facing replacement positive package. -/
theorem not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
            Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
              Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Exact one-collar current-boundary data still does not upgrade the honest closed-walk source,
Tait coloring, and endpoint witness into any current replacement positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
              Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                  Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force even the raw height-ordered or collar-layer witness-cover data. -/
theorem not_forall_some_witnessCoverData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force any of the current sufficient same-embedding geometric endpoints. -/
theorem not_forall_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
            Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- The named endpoint witness still does not upgrade the exact one-collar current-boundary
honest-source shell into any current sufficient same-embedding geometric endpoint. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  exact
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair
      (by
        intro emb source hcurrent hcolor hnonempty
        exact
          h emb source hcurrent hcolor
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty))

end Theorem49PositiveGeometricSourceReplacementRegression

end Mettapedia.GraphTheory.FourColor
