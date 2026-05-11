import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRegression

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression

namespace Theorem49ResidualBoundaryObstruction

theorem not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
        sharedInteriorPairAnnulusEmbedding) := by
  intro hResidual
  exact
    not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair
      (nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_iff_nonempty_planarBoundaryCollarLayerFacePeelWitnessData.1
        hResidual)

theorem not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair :
    ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn
      sharedInteriorPairAnnulusEmbedding := by
  intro hResidual
  exact
    not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair
      ((theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).1
        hResidual)

theorem not_nonempty_residualBoundarySelectorData_sharedInteriorPair :
    ¬ Nonempty
      (ResidualBoundarySelectorData sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  exact
    not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        data hasUnblockedInteriorEndpoint_sharedInteriorPair)

theorem nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary :
    Nonempty
      (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) := by
  exact
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      sharedInteriorPairTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)⟩

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_residualBoundaryGeometry
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding ∧
      ¬ Nonempty (ResidualBoundarySelectorData sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair⟩

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryGeometry
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn sharedInteriorPairAnnulusEmbedding := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair⟩

theorem
    not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
              HasUnblockedInteriorEndpoint emb →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
        hasUnblockedInteriorEndpoint_sharedInteriorPair)

theorem
    not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    not_forall_nonempty_residualBoundaryLayerFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
              HasUnblockedInteriorEndpoint emb →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
        hasUnblockedInteriorEndpoint_sharedInteriorPair)

theorem
    not_forall_nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
              HasUnblockedInteriorEndpoint emb →
                Nonempty (ResidualBoundarySelectorData emb) := by
  intro h
  exact
    not_nonempty_residualBoundarySelectorData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
        hasUnblockedInteriorEndpoint_sharedInteriorPair)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair⟩

theorem
    not_forall_residualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
              HasUnblockedInteriorEndpoint emb →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    hResidual | hSelector | hHeight | hCollar
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    hResidual | hSelector | hHeight | hCollar
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (ResidualBoundarySelectorData sharedInteriorPairAnnulusEmbedding) ∧
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
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    not_forall_some_knownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    hResidual | hSelector | hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    not_forall_some_knownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty
                        (BoundaryRootedFacePeelCertificate emb.faces.attach
                          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    hResidual | hSelector | hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

end Theorem49ResidualBoundaryObstruction

end Mettapedia.GraphTheory.FourColor
