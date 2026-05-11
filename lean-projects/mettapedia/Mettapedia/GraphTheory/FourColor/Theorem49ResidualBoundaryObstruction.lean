import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRegression
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression
open Theorem49ForcingInteriorEdgeObstruction

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

theorem exists_selectedBoundarySupport_of_sip01_mem_faceBoundary_sharedInteriorPair
    {f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces}
    (hf : sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1) :
    ∃ b ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1,
      b ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces := by
  rcases (sip01_mem_faceBoundary_iff f).1 hf with rfl | rfl
  · exact
      ⟨sip23,
        by
          simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary, sipFace0],
        sip23_mem_selectedBoundarySupport⟩
  · exact
      ⟨sip24,
        by
          simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary, sipFace1],
        sip24_mem_selectedBoundarySupport⟩

/-- The shared-interior-pair benchmark carries a concrete forcing interior edge `sip01`: both
incident faces already contain selected-boundary support.  This witnesses failure of the
boundary-free selector shell on the same honest embedding. -/
def sharedInteriorPairForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness sharedInteriorPairAnnulusEmbedding where
  edge := sip01
  heInterior := sip01_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_sip01_mem_faceBoundary_sharedInteriorPair hf

theorem not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector sharedInteriorPairAnnulusEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      ⟨sharedInteriorPairForcingInteriorEdgeWitness⟩

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty (BoundaryFreeIncidentFaceSelector sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair
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
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) := by
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
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair
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
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair
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
                  ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)) := by
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
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                      Nonempty
                        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair
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

theorem not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover :
    ¬ ∃ peelFaces : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
        sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1)
            (selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces
              sharedInteriorPairAnnulusEmbedding.faces)) ∧
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces hunique
            (interiorDualSpanningForestRoot sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces
              sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
              hcoverRoots hsepRoots)
            sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ ∃ peelFaces : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces),
          ∃ hunique : PairwiseUniqueSharedInteriorEdges
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces,
          ∃ hcoverRoots : RootSetCovers
            (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
          ∃ hsepRoots : RootSetSeparated
            (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
            (∀ f ∈ peelFaces,
              Disjoint (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1)
                (selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  sharedInteriorPairAnnulusEmbedding.faces)) ∧
            interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces ⊆ peelFaces.image
              (rootedSharedInteriorEdgeOfPairwiseUnique
                sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces hunique
                (interiorDualSpanningForestRoot sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                  hcoverRoots hsepRoots)
                sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
                  ∃ peelFaces : Finset (AmbientFace emb.faces),
                  ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph emb.faceBoundary emb.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph emb.faceBoundary emb.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint (emb.faceBoundary f.1)
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                    interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
                      (rootedSharedInteriorEdgeOfPairwiseUnique
                        emb.faceBoundary emb.faces hunique
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots)
                        source.fallbackEdge) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover
    :
    ¬ ∃ peelFaces : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
        sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          sharedInteriorPairAnnulusBoundaryReachabilityData
          sharedInteriorPairDartSuccessorCycleGeometry
          sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          sharedInteriorPairAnnulusBoundaryReachabilityData
          sharedInteriorPairDartSuccessorCycleGeometry
          sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1)
            (selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces
              sharedInteriorPairAnnulusEmbedding.faces)) ∧
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces hunique
            (interiorDualSpanningForestRoot sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                sharedInteriorPairAnnulusBoundaryReachabilityData
                sharedInteriorPairDartSuccessorCycleGeometry
                sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              sharedInteriorPairAnnulusBoundaryReachabilityData
              sharedInteriorPairDartSuccessorCycleGeometry
              sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).fallbackEdge) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
                      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
                      ∃ hcoverRoots : RootSetCovers
                        (interiorDualGraph emb.faceBoundary emb.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      ∃ hsepRoots : RootSetSeparated
                        (interiorDualGraph emb.faceBoundary emb.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        (∀ f ∈ peelFaces,
                          Disjoint (emb.faceBoundary f.1)
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            emb.faceBoundary emb.faces hunique
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge) := by
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
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ peelFaces : Finset (AmbientFace emb.faces),
                        ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
                        ∃ hcoverRoots : RootSetCovers
                          (interiorDualGraph emb.faceBoundary emb.faces)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        ∃ hsepRoots : RootSetSeparated
                          (interiorDualGraph emb.faceBoundary emb.faces)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                          (∀ f ∈ peelFaces,
                            Disjoint (emb.faceBoundary f.1)
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                          interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge) := by
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
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsNoInteriorEdges :
    ¬ ∃ _hcoverRoots : RootSetCovers
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces = ∅ := by
  rintro ⟨hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      sharedInteriorPairClosedWalkAnnulusBoundarySource hcoverRoots hsepRoots hnoInterior
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ ∃ _hcoverRoots : RootSetCovers
          (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces)
          sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
          ∃ _hsepRoots : RootSetSeparated
            (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
            interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces = ∅ := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
                  ∃ _hcoverRoots : RootSetCovers
                    (interiorDualGraph emb.faceBoundary emb.faces)
                    source.boundaryFaceRoots,
                  ∃ _hsepRoots : RootSetSeparated
                    (interiorDualGraph emb.faceBoundary emb.faces)
                    source.boundaryFaceRoots,
                    interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨source, hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsNoInteriorEdges :
    ¬ ∃ _hcoverRoots : RootSetCovers
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          sharedInteriorPairAnnulusBoundaryReachabilityData
          sharedInteriorPairDartSuccessorCycleGeometry
          sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated
        (interiorDualGraph sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          sharedInteriorPairAnnulusBoundaryReachabilityData
          sharedInteriorPairDartSuccessorCycleGeometry
          sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots,
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces = ∅ := by
  rintro ⟨hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcoverRoots hsepRoots hnoInterior
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ _hcoverRoots : RootSetCovers
                      (interiorDualGraph emb.faceBoundary emb.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      ∃ _hsepRoots : RootSetSeparated
                        (interiorDualGraph emb.faceBoundary emb.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
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
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ _hcoverRoots : RootSetCovers
                          (interiorDualGraph emb.faceBoundary emb.faces)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        ∃ _hsepRoots : RootSetSeparated
                          (interiorDualGraph emb.faceBoundary emb.faces)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                          interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
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
    ⟨hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcoverRoots hsepRoots hnoInterior
      hasUnblockedInteriorEndpoint_sharedInteriorPair

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
