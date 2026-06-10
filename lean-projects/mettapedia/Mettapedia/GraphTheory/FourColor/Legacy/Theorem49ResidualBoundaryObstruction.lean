import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PositiveGeometricSourceReplacementRegression
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression
open Theorem49ForcingInteriorEdgeObstruction

namespace Theorem49ResidualBoundaryObstruction

variable {V : Type*} [DecidableEq V]

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

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair :
    ¬ Nonempty
      (InteriorDualBoundaryRootAdjDistancePeelData
        sharedInteriorPairAnnulusEmbedding.faces
        sharedInteriorPairAnnulusEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem not_nonempty_interiorDualBoundaryRootParentPeelData_sharedInteriorPair :
    ¬ Nonempty
      (InteriorDualBoundaryRootParentPeelData
        sharedInteriorPairAnnulusEmbedding.faces
        sharedInteriorPairAnnulusEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootParentPeelData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusRootAdjDistancePeelData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusRootParentPeelData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_interiorDualBoundaryRootAdjDistancePeelData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (InteriorDualBoundaryRootAdjDistancePeelData
          sharedInteriorPairAnnulusEmbedding.faces
          sharedInteriorPairAnnulusEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty
                  (InteriorDualBoundaryRootAdjDistancePeelData
                    emb.faces emb.faceBoundary) := by
  intro h
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (InteriorDualBoundaryRootAdjDistancePeelData
                      emb.faces emb.faceBoundary)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty
                        (InteriorDualBoundaryRootAdjDistancePeelData
                          emb.faces emb.faceBoundary) := by
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
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootAdjDistancePeelData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusRootAdjDistancePeelData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
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
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusRootParentPeelData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty
                        (PlanarBoundaryAnnulusRootParentPeelData emb) := by
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
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

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
    exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          HasUnblockedInteriorEndpoint emb →
            Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        hasUnblockedInteriorEndpoint_sharedInteriorPair)

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
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        HasUnblockedInteriorEndpoint emb ∧
          ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          HasUnblockedInteriorEndpoint emb →
            Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hasUnblockedInteriorEndpoint_sharedInteriorPair)

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

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFacePartitionData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFacePartitionData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair
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
                    (PlanarBoundaryAnnulusConstructionFacePartitionData emb)) := by
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
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                        (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_sharedInteriorPair
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

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionPositiveFrontierData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair
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
                    (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)) := by
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
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                        (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair
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

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData
        sharedInteriorPairAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
      sharedInteriorPairForcingInteriorEdgeWitness

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
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
                    (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
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
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                        (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
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

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force the downstream positive construction face-layer package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ⟨sharedInteriorPairForcingInteriorEdgeWitness⟩⟩

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of a same-embedding
boundary-free incident-face selector from that shell. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  refine
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Exact one-collar current-boundary data still does not make the honest-source exact v23 shell
sufficient for the local boundary-free selector burden. -/
theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
      ¬ Nonempty (BoundaryFreeIncidentFaceSelector sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force the local boundary-free selector package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact v23 shell
sufficient for the local boundary-free selector package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of same-embedding
annulus-root adjacency-distance data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of same-embedding
annulus-root parent peel data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of the stronger
selected-boundary-contact construction shell from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force the selected-boundary-contact construction package. -/
theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
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
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair⟩

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force the selected-boundary-contact construction package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact v23 shell
sufficient for the selected-boundary-contact construction package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction face-partition data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction positive-frontier data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction face-layer data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force the downstream positive construction face-layer package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact v23 shell
sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h emb source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Exact one-collar current-boundary data also fails to make the honest-source exact v23/v23.5
shell sufficient to exclude forcing interior edges.  So the missing local no-forcing burden is
already present before any later face-layer lowering. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    refine ⟨emb, ?_, hforce⟩
    exact ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    exact h emb source C a b faceBoundary hcurrent hC hEndpoint hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with a forcing interior edge refutes a universal derivation of the full repaired local parent-peel
package consisting of same-split parent data, the selector-deficit selected-boundary condition,
and the older positive current-outer-boundary side conditions. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                  parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
                  (∀ f : AmbientFace emb.faces,
                    f ∈ parentData.interiorData.peelFaces →
                      f ∉
                          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).peelFaces →
                        ∃ e ∈ emb.faceBoundary f.1,
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                  (∀ i :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars,
                    0 < i.1 →
                      ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).currentOuterBoundary i).Nonempty) ∧
                  (∀ {i j :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars},
                    0 < i.1 → 0 < j.1 → i ≠ j →
                      Disjoint
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary i)
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary j)) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
    intro hforce
    rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
      ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
        hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
    exact
      false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
        source hcurrent C hv23 parentData hparentBoundary
        hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
        hcurrentOuterBoundaryDisjoint

/-- The live exact one-collar/v23 honest-source shell does not force the full repaired local
parent-peel package with selector-deficit and positive current-outer-boundary hypotheses. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                  parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
                  (∀ f : AmbientFace emb.faces,
                    f ∈ parentData.interiorData.peelFaces →
                      f ∉
                          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).peelFaces →
                        ∃ e ∈ emb.faceBoundary f.1,
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                  (∀ i :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars,
                    0 < i.1 →
                      ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).currentOuterBoundary i).Nonempty) ∧
                  (∀ {i j :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars},
                    0 < i.1 → 0 < j.1 → i ≠ j →
                      Disjoint
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary i)
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary j)) := by
  exact
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- The shared-interior-pair benchmark packages the same failure directly on the exact one-collar
honest-source shell: even with Tait coloring, a real unblocked endpoint, and the live v23
residual seed, the repaired selector-deficit plus positive current-outer-boundary parent-peel
package is still absent on that embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                      parentData.boundaryData =
                          source.toPlanarBoundaryAnnulusBoundaryData ∧
                      (∀ f : AmbientFace emb.faces,
                        f ∈ parentData.interiorData.peelFaces →
                          f ∉
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).peelFaces →
                            ∃ e ∈ emb.faceBoundary f.1,
                              e ∈
                                selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      (∀ i :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars,
                        0 < i.1 →
                          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).currentOuterBoundary i).Nonempty) ∧
                      (∀ {i j :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars},
                        0 < i.1 → 0 < j.1 → i ≠ j →
                          Disjoint
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i)
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary j))) := by
  refine
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ?_⟩
  rintro ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with a forcing interior edge also refutes the stronger older repaired parent-peel package with
non-peeled-face selected-boundary contact and the old positive current-outer-boundary side
conditions. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                  parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
                  (∀ f : AmbientFace emb.faces,
                    f ∉
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).peelFaces →
                      ∃ e ∈ emb.faceBoundary f.1,
                        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                  (∀ i :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars,
                    0 < i.1 →
                      ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).currentOuterBoundary i).Nonempty) ∧
                  (∀ {i j :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars},
                    0 < i.1 → 0 < j.1 → i ≠ j →
                      Disjoint
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary i)
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary j)) := by
  intro h
  refine
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := G) hWitness ?_
  intro emb source C a b faceBoundary hcurrent hC hEndpoint hv23
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    ⟨parentData, hparentBoundary, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  refine
    ⟨parentData, hparentBoundary, ?_, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
      parentData hnonPeelSelectedBoundary

/-- The live exact one-collar/v23 honest-source shell also does not force the older stronger
non-peeled-face selected-boundary-contact parent-peel package with positive current-outer-
boundary side conditions. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                  parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
                  (∀ f : AmbientFace emb.faces,
                    f ∉
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).peelFaces →
                      ∃ e ∈ emb.faceBoundary f.1,
                        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                  (∀ i :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars,
                    0 < i.1 →
                      ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).currentOuterBoundary i).Nonempty) ∧
                  (∀ {i j :
                      Fin
                        (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                          parentData).numCollars},
                    0 < i.1 → 0 < j.1 → i ≠ j →
                      Disjoint
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary i)
                        ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                            parentData).currentOuterBoundary j)) := by
  exact
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- The shared-interior-pair benchmark packages the stronger non-peeled-face failure directly on
the exact one-collar honest-source shell: even with Tait coloring, a real unblocked endpoint,
and the live v23 residual seed, the older non-peeled-face plus positive current-outer-boundary
parent-peel package is still absent on that embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                      parentData.boundaryData =
                          source.toPlanarBoundaryAnnulusBoundaryData ∧
                      (∀ f : AmbientFace emb.faces,
                        f ∉
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).peelFaces →
                          ∃ e ∈ emb.faceBoundary f.1,
                            e ∈
                              selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      (∀ i :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars,
                        0 < i.1 →
                          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).currentOuterBoundary i).Nonempty) ∧
                      (∀ {i j :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars},
                        0 < i.1 → 0 < j.1 → i ≠ j →
                          Disjoint
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i)
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary j))) := by
  refine
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ?_⟩
  rintro ⟨parentData, hparentBoundary, hnonPeelSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
      parentData hparentBoundary hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same exact one-collar current-boundary refinement still does not force the downstream
positive construction face-layer package on the successor-cycle boundary-order shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ⟨sharedInteriorPairForcingInteriorEdgeWitness⟩⟩

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of a same-embedding
boundary-free incident-face selector from that shell. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
        ∀ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
                    data.numCollars = 1 ∧
                      data.toPlanarBoundaryAnnulusBoundaryData =
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  refine
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb, ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h boundaryData dartCycles hselectedBoundaryArc C hC hEndpoint a b faceBoundary hcurrent hv23

/-- Even after adding exact one-collar current-boundary data, the exact v23 successor-cycle
shell still does not force the local boundary-free selector package. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data still does not make the successor-cycle exact v23
shell sufficient for the local boundary-free selector package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
                      data.numCollars = 1 ∧
                        data.toPlanarBoundaryAnnulusBoundaryData =
                          boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
                      Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                        Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of same-embedding
annulus-root adjacency-distance data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of same-embedding
annulus-root parent peel data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of the stronger
selected-boundary-contact construction shell from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- The same exact one-collar current-boundary refinement still does not force the
selected-boundary-contact construction package on the successor-cycle shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data still does not make the successor-cycle exact v23
shell sufficient for the selected-boundary-contact construction package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction face-partition data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction positive-frontier data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of same-embedding
construction face-layer data from that shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- The same exact one-collar current-boundary refinement still does not force the downstream
positive construction face-layer package on the successor-cycle boundary-order shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair⟩

/-- Joint obstruction on the actual successor-cycle exact-v23 shared-interior-pair shell: the
same fixed embedding already carries a concrete face boundary with two distinct interior edges
while still failing the upstream positive construction face-layer package.  This records the
local two-interior-edge burden directly on the live benchmark geometry. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  (∃ f : AmbientFace emb.faces,
                    ∃ e₁ ∈ emb.faceBoundary f.1,
                      ∃ e₂ ∈ emb.faceBoundary f.1,
                        e₁ ≠ e₂ ∧
                          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                          e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair⟩

/-- Joint obstruction one layer earlier in the construction lane: the exact one-collar/v23
successor-cycle shared-interior-pair shell already carries a concrete face boundary with two
distinct interior edges while still failing the positive-frontier construction package. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  (∃ f : AmbientFace emb.faces,
                    ∃ e₁ ∈ emb.faceBoundary f.1,
                      ∃ e₂ ∈ emb.faceBoundary f.1,
                        e₁ ≠ e₂ ∧
                          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                          e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact v23 shell
sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact v23/v23.5
shell sufficient to exclude forcing interior edges.  So the missing local no-forcing burden is
already present on the actual boundary-order source surface as well. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    refine ⟨emb, ?_, hforce⟩
    exact
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge refutes a universal derivation of the full repaired local
parent-peel package with selector-deficit and positive current-outer-boundary hypotheses. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                        parentData.boundaryData =
                            boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                        (∀ f : AmbientFace emb.faces,
                          f ∈ parentData.interiorData.peelFaces →
                            f ∉
                                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).peelFaces →
                              ∃ e ∈ emb.faceBoundary f.1,
                                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∀ i :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars,
                          0 < i.1 →
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i).Nonempty) ∧
                        (∀ {i j :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars},
                          0 < i.1 → 0 < j.1 → i ≠ j →
                            Disjoint
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary i)
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary j)) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := G)
      (P := fun emb =>
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23⟩
    intro hforce
    rcases h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
        faceBoundary hv23 with
      ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
        hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
    exact
      false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
        boundaryData dartCycles hSelectedBoundaryArc hcurrent C hv23 parentData hparentBoundary
        hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
        hcurrentOuterBoundaryDisjoint

/-- The live exact one-collar/v23 successor-cycle shell also does not force the full repaired
local parent-peel package with selector-deficit and positive current-outer-boundary hypotheses. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                        parentData.boundaryData =
                            boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                        (∀ f : AmbientFace emb.faces,
                          f ∈ parentData.interiorData.peelFaces →
                            f ∉
                                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).peelFaces →
                              ∃ e ∈ emb.faceBoundary f.1,
                                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∀ i :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars,
                          0 < i.1 →
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i).Nonempty) ∧
                        (∀ {i j :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars},
                          0 < i.1 → 0 < j.1 → i ≠ j →
                            Disjoint
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary i)
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary j)) := by
  exact
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- The shared-interior-pair benchmark also packages that same failure directly on the exact
one-collar successor-cycle shell.  So the route-facing boundary-order interface itself still does
not force the repaired selector-deficit plus positive current-outer-boundary parent-peel shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                      parentData.boundaryData =
                          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                      (∀ f : AmbientFace emb.faces,
                        f ∈ parentData.interiorData.peelFaces →
                          f ∉
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).peelFaces →
                            ∃ e ∈ emb.faceBoundary f.1,
                              e ∈
                                selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      (∀ i :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars,
                        0 < i.1 →
                          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).currentOuterBoundary i).Nonempty) ∧
                      (∀ {i j :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars},
                        0 < i.1 → 0 < j.1 → i ≠ j →
                          Disjoint
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i)
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary j))) := by
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
  refine
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ?_⟩
  rintro ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with a forcing interior edge also refutes the stronger older repaired parent-peel
package with non-peeled-face selected-boundary contact and the old positive current-outer-
boundary side conditions. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                        parentData.boundaryData =
                            boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                        (∀ f : AmbientFace emb.faces,
                          f ∉
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).peelFaces →
                            ∃ e ∈ emb.faceBoundary f.1,
                              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∀ i :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars,
                          0 < i.1 →
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i).Nonempty) ∧
                        (∀ {i j :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars},
                          0 < i.1 → 0 < j.1 → i ≠ j →
                            Disjoint
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary i)
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary j)) := by
  intro h
  refine
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := G) hWitness ?_
  intro emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b faceBoundary
    hv23
  rcases h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hEndpoint a b
      faceBoundary hv23 with
    ⟨parentData, hparentBoundary, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  refine
    ⟨parentData, hparentBoundary, ?_, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
      parentData hnonPeelSelectedBoundary

/-- The live exact one-collar/v23 successor-cycle shell also does not force the older stronger
non-peeled-face selected-boundary-contact parent-peel package with positive current-outer-
boundary side conditions. -/
theorem
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                        parentData.boundaryData =
                            boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                        (∀ f : AmbientFace emb.faces,
                          f ∉
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).peelFaces →
                            ∃ e ∈ emb.faceBoundary f.1,
                              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∀ i :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars,
                          0 < i.1 →
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i).Nonempty) ∧
                        (∀ {i j :
                            Fin
                              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).numCollars},
                          0 < i.1 → 0 < j.1 → i ≠ j →
                            Disjoint
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary i)
                              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                  parentData).currentOuterBoundary j)) := by
  exact
    not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness
      (G := sharedInteriorPairAnnulusGraph)
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_sharedInteriorPair

/-- The shared-interior-pair benchmark also packages that stronger failure directly on the exact
one-collar successor-cycle shell.  So the route-facing boundary-order interface itself still does
not force even the older non-peeled-face plus positive current-outer-boundary parent-peel shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
                      parentData.boundaryData =
                          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
                      (∀ f : AmbientFace emb.faces,
                        f ∉
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).peelFaces →
                          ∃ e ∈ emb.faceBoundary f.1,
                            e ∈
                              selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      (∀ i :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars,
                        0 < i.1 →
                          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).currentOuterBoundary i).Nonempty) ∧
                      (∀ {i j :
                          Fin
                            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                              parentData).numCollars},
                        0 < i.1 → 0 < j.1 → i ≠ j →
                          Disjoint
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary i)
                            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                                parentData).currentOuterBoundary j))) := by
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
  refine
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ?_⟩
  rintro ⟨parentData, hparentBoundary, hnonPeelSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
      parentData hparentBoundary hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

theorem
    not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    :
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
            sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈
            (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
              (rootedSharedInteriorEdgeOfPairwiseUnique
                sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces hunique
                (interiorDualSpanningForestRoot
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                  hcoverRoots hsepRoots)
                sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge f),
          e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces
                sharedInteriorPairAnnulusEmbedding.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces).Adj f g ∧
              e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1 ∧
              (interiorDualSpanningForest
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces).dist
                  f
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces).dist
                  g
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                    hcoverRoots hsepRoots g)) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair
      ⟨interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        sharedInteriorPairClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        HasUnblockedInteriorEndpoint emb ∧
          ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                    source.fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                      e ∈ emb.faceBoundary g.1 ∧
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          f
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots f) <
                        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          g
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots g)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
        HasUnblockedInteriorEndpoint emb →
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
                  source.fallbackEdge) ∧
              (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    emb.faceBoundary emb.faces hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      source.boundaryFaceRoots hcoverRoots hsepRoots)
                    source.fallbackEdge f),
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                  ∃ g ∈ peelFaces,
                    (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                    e ∈ emb.faceBoundary g.1 ∧
                    (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                        f
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots f) <
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                        g
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots g)) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
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
                sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
            (∀ f ∈ peelFaces, ∀ e ∈
                (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces hunique
                    (interiorDualSpanningForestRoot
                      sharedInteriorPairAnnulusEmbedding.faceBoundary
                      sharedInteriorPairAnnulusEmbedding.faces
                      sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                      hcoverRoots hsepRoots)
                    sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge f),
              e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    sharedInteriorPairAnnulusEmbedding.faces ∨
                ∃ g ∈ peelFaces,
                  (interiorDualSpanningForest
                      sharedInteriorPairAnnulusEmbedding.faceBoundary
                      sharedInteriorPairAnnulusEmbedding.faces).Adj f g ∧
                  e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1 ∧
                  (interiorDualSpanningForest
                      sharedInteriorPairAnnulusEmbedding.faceBoundary
                      sharedInteriorPairAnnulusEmbedding.faces).dist
                      f
                      (interiorDualSpanningForestRoot
                        sharedInteriorPairAnnulusEmbedding.faceBoundary
                        sharedInteriorPairAnnulusEmbedding.faces
                        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                        hcoverRoots hsepRoots f) <
                    (interiorDualSpanningForest
                        sharedInteriorPairAnnulusEmbedding.faceBoundary
                        sharedInteriorPairAnnulusEmbedding.faces).dist
                      g
                      (interiorDualSpanningForestRoot
                        sharedInteriorPairAnnulusEmbedding.faceBoundary
                        sharedInteriorPairAnnulusEmbedding.faces
                        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                        hcoverRoots hsepRoots g)) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots)
                              source.fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                              e ∈ emb.faceBoundary g.1 ∧
                              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                  f
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    source.boundaryFaceRoots hcoverRoots hsepRoots f) <
                                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                  g
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    source.boundaryFaceRoots hcoverRoots hsepRoots g))) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                          e ∈ emb.faceBoundary g.1 ∧
                          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                              f
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
                            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                              g
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots g)) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩

theorem
    not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
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
              sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈
            (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
              (rootedSharedInteriorEdgeOfPairwiseUnique
                sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces hunique
                (interiorDualSpanningForestRoot
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    sharedInteriorPairAnnulusBoundaryReachabilityData
                    sharedInteriorPairDartSuccessorCycleGeometry
                    sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
                  hcoverRoots hsepRoots)
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  sharedInteriorPairAnnulusBoundaryReachabilityData
                  sharedInteriorPairDartSuccessorCycleGeometry
                  sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).fallbackEdge
                f),
          e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces
                sharedInteriorPairAnnulusEmbedding.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces).Adj f g ∧
              e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1 ∧
              (interiorDualSpanningForest
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces).dist
                  f
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      sharedInteriorPairAnnulusBoundaryReachabilityData
                      sharedInteriorPairDartSuccessorCycleGeometry
                      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces).dist
                  g
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      sharedInteriorPairAnnulusBoundaryReachabilityData
                      sharedInteriorPairDartSuccessorCycleGeometry
                      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
                    hcoverRoots hsepRoots g)) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair
      ⟨interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        HasUnblockedInteriorEndpoint emb ∧
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
                      boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                        hcoverRoots hsepRoots)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                      e ∈ emb.faceBoundary g.1 ∧
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          f
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots f) <
                        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          g
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots g)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          HasUnblockedInteriorEndpoint emb →
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
                      boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                        hcoverRoots hsepRoots)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                      e ∈ emb.faceBoundary g.1 ∧
                      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          f
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots f) <
                        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                          g
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots g)) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                              e ∈ emb.faceBoundary g.1 ∧
                              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                  f
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots f) <
                                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                  g
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots g)) := by
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
      Classical.choose hcurrent,
      (Classical.choose_spec hcurrent).1,
      (Classical.choose_spec hcurrent).2,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
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
                                  boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                            (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                                (rootedSharedInteriorEdgeOfPairwiseUnique
                                  emb.faceBoundary emb.faces hunique
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots)
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).fallbackEdge f),
                              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                                ∃ g ∈ peelFaces,
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
                                  e ∈ emb.faceBoundary g.1 ∧
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                      f
                                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                        hcoverRoots hsepRoots f) <
                                    (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                                      g
                                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                        hcoverRoots hsepRoots g)) := by
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩

theorem
    not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    :
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
            sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈
            (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
              (rootedSharedInteriorEdgeOfPairwiseUnique
                sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces hunique
                (interiorDualSpanningForestRoot
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                  hcoverRoots hsepRoots)
                sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge f),
          e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces
                sharedInteriorPairAnnulusEmbedding.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot
                  (interiorDualSpanningForest
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces)
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        HasUnblockedInteriorEndpoint emb ∧
          ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                    source.fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

/-- The shared-interior-pair benchmark already refutes any universal derivation of the stronger
closed-walk face-membership shell from honest source data plus the current endpoint witness
alone; the exact v23 seed and the Tait coloring are not needed for this obstruction. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          HasUnblockedInteriorEndpoint emb →
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
                    source.fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  exact
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
      (G := sharedInteriorPairAnnulusGraph)
      ⟨sharedInteriorPairAnnulusEmbedding,
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
        hasUnblockedInteriorEndpoint_sharedInteriorPair⟩

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
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
                sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
            (∀ f ∈ peelFaces, ∀ e ∈
                (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces hunique
                    (interiorDualSpanningForestRoot
                      sharedInteriorPairAnnulusEmbedding.faceBoundary
                      sharedInteriorPairAnnulusEmbedding.faces
                      sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                      hcoverRoots hsepRoots)
                    sharedInteriorPairClosedWalkAnnulusBoundarySource.fallbackEdge f),
              e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    sharedInteriorPairAnnulusEmbedding.faces ∨
                ∃ g ∈ peelFaces,
                  parentTowardsRoot
                      (interiorDualSpanningForest
                        sharedInteriorPairAnnulusEmbedding.faceBoundary
                        sharedInteriorPairAnnulusEmbedding.faces)
                      (interiorDualSpanningForestRoot
                        sharedInteriorPairAnnulusEmbedding.faceBoundary
                        sharedInteriorPairAnnulusEmbedding.faces
                        sharedInteriorPairClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                        hcoverRoots hsepRoots) g = some f ∧
                  e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the honest closed-walk exact v23 shell together with
`HasUnblockedInteriorEndpoint` already refutes a universal derivation of the stricter
source-fixed canonical-parent shared-edge face-membership package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧
          HasUnblockedInteriorEndpoint emb ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset G.edgeSet,
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring G C →
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with ⟨emb, hSource, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
  rcases h emb C a b faceBoundary hSource hC hEndpoint hv23 with
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- Any explicit same-embedding witness of the honest closed-walk exact v23 shell together with
`HasUnblockedInteriorEndpoint` already refutes a universal derivation of the source-fixed raw
canonical-parent shared-edge cover package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧
          HasUnblockedInteriorEndpoint emb ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset G.edgeSet,
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring G C →
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
  rcases hWitness with ⟨emb, hSource, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
  rcases h emb C a b faceBoundary hSource hC hEndpoint hv23 with
    ⟨source', peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source' peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots)
                              source.fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with `HasUnblockedInteriorEndpoint` already refutes a universal derivation of the stricter
source-fixed canonical-parent shared-edge face-membership package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with `HasUnblockedInteriorEndpoint` already refutes a universal derivation of the source-fixed raw
canonical-parent shared-edge cover package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
  rcases hWitness with ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

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
    exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        HasUnblockedInteriorEndpoint emb ∧
          ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          HasUnblockedInteriorEndpoint emb →
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
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

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
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
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
              sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈
            (sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).erase
              (rootedSharedInteriorEdgeOfPairwiseUnique
                sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces hunique
                (interiorDualSpanningForestRoot
                  sharedInteriorPairAnnulusEmbedding.faceBoundary
                  sharedInteriorPairAnnulusEmbedding.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    sharedInteriorPairAnnulusBoundaryReachabilityData
                    sharedInteriorPairDartSuccessorCycleGeometry
                    sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
                  hcoverRoots hsepRoots)
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  sharedInteriorPairAnnulusBoundaryReachabilityData
                  sharedInteriorPairDartSuccessorCycleGeometry
                  sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).fallbackEdge
                f),
          e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
                sharedInteriorPairAnnulusEmbedding.faces
                sharedInteriorPairAnnulusEmbedding.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot
                  (interiorDualSpanningForest
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces)
                  (interiorDualSpanningForestRoot
                    sharedInteriorPairAnnulusEmbedding.faceBoundary
                    sharedInteriorPairAnnulusEmbedding.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      sharedInteriorPairAnnulusBoundaryReachabilityData
                      sharedInteriorPairDartSuccessorCycleGeometry
                      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary g.1) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        HasUnblockedInteriorEndpoint emb ∧
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
                      boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                        hcoverRoots hsepRoots)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

/-- The same seed-free converse failure already holds on the actual successor-cycle shell:
boundary reachability, successor-cycle selected arcs, and the current endpoint witness on the
shared-interior-pair annulus still do not universally force the stronger face-membership shell. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          HasUnblockedInteriorEndpoint emb →
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
                      boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                        hcoverRoots hsepRoots)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  exact
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint
      (G := sharedInteriorPairAnnulusGraph)
      ⟨sharedInteriorPairAnnulusEmbedding,
        sharedInteriorPairAnnulusBoundaryReachabilityData,
        sharedInteriorPairDartSuccessorCycleGeometry,
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
        rfl,
        hasUnblockedInteriorEndpoint_sharedInteriorPair⟩

/-- Any explicit same-embedding witness of the successor-cycle exact v23 shell together with
`HasUnblockedInteriorEndpoint` already refutes a universal derivation of the source-fixed raw
canonical-parent shared-edge cover package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
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
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, _hboundaryEq, C, hC, hEndpoint, a, b,
      faceBoundary, hv23⟩
  rcases h emb boundaryData dartCycles hboundaryArc C hC hEndpoint a b faceBoundary hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1) := by
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
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                          (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                              (rootedSharedInteriorEdgeOfPairwiseUnique
                                emb.faceBoundary emb.faces hunique
                                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                  hcoverRoots hsepRoots)
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).fallbackEdge f),
                            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                              ∃ g ∈ peelFaces,
                                parentTowardsRoot
                                    (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                      hcoverRoots hsepRoots) g = some f ∧
                                e ∈ emb.faceBoundary g.1) := by
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
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the successor-cycle exact v23 shell together with
`HasUnblockedInteriorEndpoint` already refutes a universal derivation of the stricter
source-fixed canonical-parent shared-edge face-membership package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                          (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                              (rootedSharedInteriorEdgeOfPairwiseUnique
                                emb.faceBoundary emb.faces hunique
                                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                  hcoverRoots hsepRoots)
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).fallbackEdge f),
                            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                              ∃ g ∈ peelFaces,
                                parentTowardsRoot
                                    (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                      hcoverRoots hsepRoots) g = some f ∧
                                e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, _hboundaryEq, C, hC, hEndpoint, a, b,
      faceBoundary, hv23⟩
  rcases h emb boundaryData dartCycles hboundaryArc C hC hEndpoint a b faceBoundary hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with `HasUnblockedInteriorEndpoint` already refutes a universal derivation of the
source-fixed raw canonical-parent shared-edge cover package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                HasUnblockedInteriorEndpoint emb →
                  ∀ a b : Color,
                    ∀ faceBoundary : Finset G.edgeSet,
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
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1) := by
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
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
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
                                  boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                            (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                                (rootedSharedInteriorEdgeOfPairwiseUnique
                                  emb.faceBoundary emb.faces hunique
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots)
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).fallbackEdge f),
                              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                                ∃ g ∈ peelFaces,
                                  parentTowardsRoot
                                      (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                        hcoverRoots hsepRoots) g = some f ∧
                                  e ∈ emb.faceBoundary g.1) := by
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with `HasUnblockedInteriorEndpoint` already refutes a universal derivation of the
stricter source-fixed canonical-parent shared-edge face-membership package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                HasUnblockedInteriorEndpoint emb →
                  ∀ a b : Color,
                    ∀ faceBoundary : Finset G.edgeSet,
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
                                  boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                            (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                                (rootedSharedInteriorEdgeOfPairwiseUnique
                                  emb.faceBoundary emb.faces hunique
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots)
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).fallbackEdge f),
                              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                                ∃ g ∈ peelFaces,
                                  parentTowardsRoot
                                      (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                        hcoverRoots hsepRoots) g = some f ∧
                                  e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, _hboundaryEq, hcurrent, C, hC, hEndpoint, a, b,
      faceBoundary, hv23⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

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
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        HasUnblockedInteriorEndpoint emb ∧
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
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          HasUnblockedInteriorEndpoint emb →
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
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
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

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
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
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
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
    exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        HasUnblockedInteriorEndpoint emb ∧
          ¬ ∃ _hcoverRoots : RootSetCovers
              (interiorDualGraph emb.faceBoundary emb.faces)
              source.boundaryFaceRoots,
              ∃ _hsepRoots : RootSetSeparated
                (interiorDualGraph emb.faceBoundary emb.faces)
                source.boundaryFaceRoots,
                interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          HasUnblockedInteriorEndpoint emb →
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
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨source, hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior
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

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ _hcoverRoots : RootSetCovers
                      (interiorDualGraph emb.faceBoundary emb.faces)
                      source.boundaryFaceRoots,
                      ∃ _hsepRoots : RootSetSeparated
                        (interiorDualGraph emb.faceBoundary emb.faces)
                        source.boundaryFaceRoots,
                        interiorEdgeSupport emb.faceBoundary emb.faces = ∅) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                ∃ _hcoverRoots : RootSetCovers
                    (interiorDualGraph emb.faceBoundary emb.faces)
                    source.boundaryFaceRoots,
                    ∃ _hsepRoots : RootSetSeparated
                      (interiorDualGraph emb.faceBoundary emb.faces)
                      source.boundaryFaceRoots,
                      interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  intro h
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    ⟨hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      sharedInteriorPairClosedWalkAnnulusBoundarySource hcoverRoots hsepRoots hnoInterior
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
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        HasUnblockedInteriorEndpoint emb ∧
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
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          HasUnblockedInteriorEndpoint emb →
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
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    ⟨hcoverRoots, hsepRoots, hnoInterior⟩
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
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
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
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsNoInteriorEdges⟩

theorem
    not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
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

/-- Honest source data, a Tait coloring, and the current endpoint witness on the
shared-interior-pair benchmark still do not universally force even the combined
local selector, source-fixed canonical-parent shells, or the previously known
same-embedding residual-geometry burden. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
              HasUnblockedInteriorEndpoint emb →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                        source.fallbackEdge)) ∨
                (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1)) ∨
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
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    hSelector | hRaw | hFaceMembership | hResidual | hResidualSelector | hHeight | hCollar |
      hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair hSelector
  · rcases hRaw with ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · rcases hFaceMembership with
      ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hResidualSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- The same bundled seed-free failure already holds on the actual successor-cycle
boundary-order shell: selected-boundary arcs plus the current endpoint witness do not
universally force any selector, canonical-parent, or previously known same-embedding
geometry package on the shared-interior-pair annulus. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
              (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        boundaryData dartCycles hboundaryArc).fallbackEdge)) ∨
              (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                  (∀ f ∈ peelFaces, ∀ e ∈
                      (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).fallbackEdge f),
                    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                      ∃ g ∈ peelFaces,
                        parentTowardsRoot
                            (interiorDualSpanningForest emb.faceBoundary emb.faces)
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots) g = some f ∧
                        e ∈ emb.faceBoundary g.1)) ∨
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
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair with
    hSelector | hRaw | hFaceMembership | hResidual | hResidualSelector | hHeight | hCollar |
      hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair hSelector
  · rcases hRaw with ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · rcases hFaceMembership with
      ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hResidualSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- The shared-interior-pair benchmark simultaneously witnesses failure of the whole local
selector/canonical-parent/known-same-embedding burden on the honest source shell under an
actual Tait coloring and the current endpoint witness. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
            (¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge)) ∧
            (¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge) ∧
                  (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                      (rootedSharedInteriorEdgeOfPairwiseUnique
                        emb.faceBoundary emb.faces hunique
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots)
                        source.fallbackEdge f),
                    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                      ∃ g ∈ peelFaces,
                        parentTowardsRoot
                            (interiorDualSpanningForest emb.faceBoundary emb.faces)
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                        e ∈ emb.faceBoundary g.1)) ∧
            ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
            ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
            ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
            ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
            ¬ Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
            ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
            ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) := by
  refine ⟨sharedInteriorPairAnnulusEmbedding, nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
    sharedInteriorPairTaitEdgeColoring, sharedInteriorPairTaitEdgeColoring_isTait,
    hasUnblockedInteriorEndpoint_sharedInteriorPair,
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair, ?_, ?_,
    not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
    not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩
  · rintro ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · rintro ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the honest-source shell together with simultaneous
failure of the local selector, canonical-parent, and known same-embedding geometry surfaces
already refutes a universal derivation of that whole bundled burden. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
            (¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge)) ∧
            (¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge) ∧
                  (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                      (rootedSharedInteriorEdgeOfPairwiseUnique
                        emb.faceBoundary emb.faces hunique
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots)
                        source.fallbackEdge f),
                    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                      ∃ g ∈ peelFaces,
                        parentTowardsRoot
                            (interiorDualSpanningForest emb.faceBoundary emb.faces)
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                        e ∈ emb.faceBoundary g.1)) ∧
            ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
            ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
            ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
            ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
            ¬ Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
            ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
            ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
              (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge)) ∨
              (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                      source.fallbackEdge) ∧
                  (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                      (rootedSharedInteriorEdgeOfPairwiseUnique
                        emb.faceBoundary emb.faces hunique
                        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots)
                        source.fallbackEdge f),
                    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                      ∃ g ∈ peelFaces,
                        parentTowardsRoot
                            (interiorDualSpanningForest emb.faceBoundary emb.faces)
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                        e ∈ emb.faceBoundary g.1)) ∨
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
  rcases hWitness with
    ⟨emb, hsource, C, hC, hEndpoint, hSelector, hRaw, hFaceMembership, hResidual,
      hResidualSelector, hHeight, hCollar, hAttached, hWellFounded, hAnnulus⟩
  rcases h emb hsource ⟨C, hC⟩ hEndpoint with
    hSelector' | hRaw' | hFaceMembership' | hResidual' | hResidualSelector' | hHeight' |
      hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hSelector hSelector'
  · exact hRaw hRaw'
  · exact hFaceMembership hFaceMembership'
  · exact hResidual hResidual'
  · exact hResidualSelector hResidualSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

/-- The same benchmark simultaneously witnesses failure of the whole local
selector/canonical-parent/known-same-embedding burden on the live successor-cycle
selected-arc shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair
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
              ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
              (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                          boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
              (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                          boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈
                        (emb.faceBoundary f.1).erase
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            emb.faceBoundary emb.faces hunique
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1)) ∧
              ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
              ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              ¬ Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  refine ⟨sharedInteriorPairAnnulusEmbedding, sharedInteriorPairAnnulusBoundaryReachabilityData,
    sharedInteriorPairDartSuccessorCycleGeometry,
    sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
    sharedInteriorPairTaitEdgeColoring, sharedInteriorPairTaitEdgeColoring_isTait,
    hasUnblockedInteriorEndpoint_sharedInteriorPair,
    not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair, ?_, ?_,
    not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
    not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
    not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩
  · rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair
  · rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, _hchildren⟩
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hasUnblockedInteriorEndpoint_sharedInteriorPair

/-- Any explicit same-embedding witness of the live successor-cycle shell together with
simultaneous failure of the local selector, canonical-parent, and known same-embedding
geometry surfaces already refutes a universal derivation of that whole bundled burden. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
              (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                          boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
              (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                          boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈
                        (emb.faceBoundary f.1).erase
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            emb.faceBoundary emb.faces hunique
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1)) ∧
              ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
              ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              ¬ Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
              (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
                |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C) →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
              (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        boundaryData dartCycles hboundaryArc).fallbackEdge)) ∨
              (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                  (∀ f ∈ peelFaces, ∀ e ∈
                      (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots)
                          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                            boundaryData dartCycles hboundaryArc).fallbackEdge f),
                    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                      ∃ g ∈ peelFaces,
                        parentTowardsRoot
                            (interiorDualSpanningForest emb.faceBoundary emb.faces)
                            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots) g = some f ∧
                        e ∈ emb.faceBoundary g.1)) ∨
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
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, C, hC, hEndpoint, hSelector, hRaw,
      hFaceMembership, hResidual, hResidualSelector, hHeight, hCollar, hAttached,
      hWellFounded, hAnnulus⟩
  rcases h emb boundaryData dartCycles hboundaryArc ⟨C, hC⟩ hEndpoint with
    hSelector' | hRaw' | hFaceMembership' | hResidual' | hResidualSelector' | hHeight' |
      hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hSelector hSelector'
  · exact hRaw hRaw'
  · exact hFaceMembership hFaceMembership'
  · exact hResidual hResidual'
  · exact hResidualSelector hResidualSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

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

/-- Even the exact one-collar current-boundary refinement of the honest-source v23 shell still
does not force residual positive geometry on the shared-interior-pair benchmark. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
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

/-- Adding exact one-collar current-boundary data still does not make the v23 honest-source
shell sufficient for residual positive geometry. -/
theorem
    not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  intro h
  exact
    not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
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

/-- The exact one-collar current-boundary refinement of the successor-cycle v23 shell is still
too weak to force residual positive geometry on the shared-interior-pair benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb) := by
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

/-- Exact one-collar current-boundary data still does not make the successor-cycle v23 shell
sufficient for residual positive geometry. -/
theorem
    not_forall_residualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
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
  exact
    not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
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

/-- Even after adjoining exact one-collar current-boundary data, the shared-interior-pair
endpoint-bearing exact-v23 honest-source shell still fails every current natural residual
same-embedding witness package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

/-- The named unblocked endpoint still does not make the exact one-collar/v23 honest-source
shared-interior-pair shell sufficient for any current natural residual same-embedding witness
package. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
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
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_sharedInteriorPair with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hResidual, hSelector,
      hHeight, hCollar⟩
  rcases h emb source hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hResidual' | hSelector' | hHeight' | hCollar'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with simultaneous failure of every current natural residual
same-embedding endpoint already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ (C : G.EdgeColoring Color),
              IsTaitEdgeColoring G C →
                HasUnblockedInteriorEndpoint emb →
                  ∀ a b : Color,
                    ∀ faceBoundary : Finset G.edgeSet,
                      Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                          Nonempty (ResidualBoundarySelectorData emb) ∨
                          Nonempty
                            (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                          Nonempty
                            (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hResidual, hSelector,
      hHeight, hCollar⟩
  rcases h emb source hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hResidual' | hSelector' | hHeight' | hCollar'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'

/-- Even after adjoining exact one-collar current-boundary data, the shared-interior-pair
endpoint-bearing exact-v23 successor-cycle shell still fails every current natural residual
same-embedding witness package. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_sharedInteriorPair
    :
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
        ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

/-- The named unblocked endpoint still does not make the exact one-collar/v23 successor-cycle
shared-interior-pair shell sufficient for any current natural residual same-embedding witness
package. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_sharedInteriorPair with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
      faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hResidual' | hSelector' | hHeight' | hCollar'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with simultaneous failure of every current natural residual
same-embedding endpoint already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb),
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ (C : G.EdgeColoring Color),
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                        Nonempty (ResidualBoundarySelectorData emb) ∨
                        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
      faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hResidual' | hSelector' | hHeight' | hCollar'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Even the exact one-collar current-boundary refinement of the honest-source v23 shell still
does not force same-embedding well-founded face-peel witness data. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair⟩

/-- Even the exact one-collar current-boundary refinement of the honest-source v23 shell still
does not force same-embedding annulus-collar geometry. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    not_forall_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairClosedWalkAnnulusBoundarySource
        sharedInteriorPairTaitEdgeColoring
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          sharedInteriorPairClosedWalkAnnulusBoundarySource)
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

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

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still fails every currently known same-embedding residual-geometry route. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
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

/-- Exact one-collar current-boundary data still does not repair the known same-embedding v23
residual geometry ladders on the honest closed-walk source shell. -/
theorem
    not_forall_some_knownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with simultaneous failure of every currently known same-embedding geometry surface already
refutes a universal derivation of that whole disjunctive geometry burden. -/
theorem
    not_forall_some_knownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
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
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hResidual, hSelector,
      hHeight, hCollar, hAttached, hWellFounded, hAnnulus⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    hResidual' | hSelector' | hHeight' | hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- The exact one-collar successor-cycle v23 shell is also too weak to force same-embedding
well-founded face-peel witness data. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair⟩

/-- The exact one-collar successor-cycle v23 shell is also too weak to force same-embedding
annulus-collar geometry. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusCollarGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
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
  exact
    not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

theorem
    not_forall_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
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
  exact
    not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        sharedInteriorPairTaitEdgeColoring
        sharedInteriorPairTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_sharedInteriorPair
        red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
        nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary)

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

/-- The same exact one-collar current-boundary refinement still does not repair any currently
known same-embedding residual-geometry route on the successor-cycle boundary-order shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry_sharedInteriorPair
    :
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

/-- Exact one-collar current-boundary data also fails to repair the known same-embedding v23
residual geometry ladders on the successor-cycle boundary-order shell. -/
theorem
    not_forall_some_knownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
carrying simultaneous failure of every currently known same-embedding geometry surface already
refutes a universal derivation of that whole disjunctive geometry burden. -/
theorem
    not_forall_some_knownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
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
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23, hResidual, hSelector, hHeight, hCollar, hAttached, hWellFounded, hAnnulus⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hResidual' | hSelector' | hHeight' | hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hResidual hResidual'
  · exact hSelector hSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

/-- The exact one-collar/v23 honest-source shell on the shared-interior-pair benchmark already
fails the whole bundled selector, canonical-parent, and previously known same-embedding geometry
burden at once. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge)) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots)
                              source.fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1)) ∧
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover,
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data and the exact v23 seed still do not make the honest
source shell sufficient for any selector, canonical-parent, or previously known same-embedding
geometry package on the shared-interior-pair benchmark. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        source.fallbackEdge)) ∨
                (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1)) ∨
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
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    hSelector | hRaw | hFaceMembership | hResidual | hResidualSelector | hHeight | hCollar |
      hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair hSelector
  · exact not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover hRaw
  · exact
      not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        hFaceMembership
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hResidualSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- The same exact one-collar/v23 strengthening collapses the whole bundled selector,
canonical-parent, and known same-embedding geometry burden on the actual successor-cycle shell
as well. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1)) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
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
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover,
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_residualBoundarySelectorData_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Exact one-collar current-boundary data and the exact v23 seed likewise fail to make the
successor-cycle shell sufficient for any selector, canonical-parent, or previously known
same-embedding geometry package on the shared-interior-pair benchmark. -/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                      (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge)) ∨
                      (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                          (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                              (rootedSharedInteriorEdgeOfPairwiseUnique
                                emb.faceBoundary emb.faces hunique
                                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                  hcoverRoots hsepRoots)
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).fallbackEdge f),
                            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                              ∃ g ∈ peelFaces,
                                parentTowardsRoot
                                    (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                      hcoverRoots hsepRoots) g = some f ∧
                                e ∈ emb.faceBoundary g.1)) ∨
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
  rcases h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary with
    hSelector | hRaw | hFaceMembership | hResidual | hResidualSelector | hHeight | hCollar |
      hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_boundaryFreeIncidentFaceSelector_sharedInteriorPair hSelector
  · exact not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover hRaw
  · exact
      not_exists_sharedInteriorPairSuccessorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        hFaceMembership
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_sharedInteriorPair hResidualSelector
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell
together with simultaneous failure of the local selector, canonical-parent, and known
same-embedding geometry surfaces already refutes a universal derivation of that bundled burden.
-/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge)) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                            source.fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots)
                              source.fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1)) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        source.fallbackEdge)) ∨
                (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                        source.fallbackEdge) ∧
                    (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          emb.faceBoundary emb.faces hunique
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge f),
                      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                        ∃ g ∈ peelFaces,
                          parentTowardsRoot
                              (interiorDualSpanningForest emb.faceBoundary emb.faces)
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                          e ∈ emb.faceBoundary g.1)) ∨
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
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hSelector, hRaw,
      hFaceMembership, hResidual, hResidualSelector, hHeight, hCollar, hAttached, hWellFounded,
      hAnnulus⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    hSelector' | hRaw' | hFaceMembership' | hResidual' | hResidualSelector' | hHeight' |
      hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hSelector hSelector'
  · exact hRaw hRaw'
  · exact hFaceMembership hFaceMembership'
  · exact hResidual hResidual'
  · exact hResidualSelector hResidualSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with simultaneous failure of the local selector, canonical-parent, and known
same-embedding geometry surfaces already refutes a universal derivation of that bundled burden.
-/
theorem
    not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                  (¬ ∃ peelFaces : Finset (AmbientFace emb.faces),
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              emb.faceBoundary emb.faces hunique
                              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge f),
                          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                            ∃ g ∈ peelFaces,
                              parentTowardsRoot
                                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                    hcoverRoots hsepRoots) g = some f ∧
                              e ∈ emb.faceBoundary g.1)) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                      (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge)) ∨
                      (∃ peelFaces : Finset (AmbientFace emb.faces),
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
                                boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                          (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                              (rootedSharedInteriorEdgeOfPairwiseUnique
                                emb.faceBoundary emb.faces hunique
                                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                  hcoverRoots hsepRoots)
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).fallbackEdge f),
                            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                              ∃ g ∈ peelFaces,
                                parentTowardsRoot
                                    (interiorDualSpanningForest emb.faceBoundary emb.faces)
                                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                      hcoverRoots hsepRoots) g = some f ∧
                                e ∈ emb.faceBoundary g.1)) ∨
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
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23, hSelector, hRaw, hFaceMembership, hResidual, hResidualSelector, hHeight, hCollar,
      hAttached, hWellFounded, hAnnulus⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hSelector' | hRaw' | hFaceMembership' | hResidual' | hResidualSelector' | hHeight' |
      hCollar' | hAttached' | hWellFounded' | hAnnulus'
  · exact hSelector hSelector'
  · exact hRaw hRaw'
  · exact hFaceMembership hFaceMembership'
  · exact hResidual hResidual'
  · exact hResidualSelector hResidualSelector'
  · exact hHeight hHeight'
  · exact hCollar hCollar'
  · exact hAttached hAttached'
  · exact hWellFounded hWellFounded'
  · exact hAnnulus hAnnulus'

theorem
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph sharedInteriorPairTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint sharedInteriorPairAnnulusEmbedding ∧
      Nonempty
        (V23ResidualBoundaryInitialState sharedInteriorPairTaitEdgeColoring red blue
          (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)) ∧
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
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Even after adding exact one-collar current-boundary data, the exact v23 honest-source shell
still does not force any current direct or route-facing replacement-positive package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
    :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
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

/-- Exact one-collar current-boundary data still does not make the honest-source exact v23 shell
sufficient for any current replacement-positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      sharedInteriorPairTaitEdgeColoring
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest-source shell together
with simultaneous failure of every current replacement-positive endpoint already refutes a
universal derivation of that direct-or-route-facing positive disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hHeight, hCollar,
      hClosedWalk, hSuccessorCycle⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with
    hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
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
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
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
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- The same exact one-collar current-boundary refinement still does not force any current direct
or route-facing replacement-positive package on the successor-cycle boundary-order shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

/-- Joint obstruction on the actual successor-cycle exact-v23 shared-interior-pair shell: the
same fixed embedding already carries a concrete face boundary with two distinct interior edges
while still failing every current direct and route-facing replacement-positive package.  This
records the upstream positive obstruction directly on the live benchmark geometry itself. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
    :
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
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  (∃ f : AmbientFace emb.faces,
                    ∃ e₁ ∈ emb.faceBoundary f.1,
                      ∃ e₂ ∈ emb.faceBoundary f.1,
                        e₁ ≠ e₂ ∧
                          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                          e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
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
      sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_sharedInteriorPair,
      red, blue,
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1),
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary,
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair⟩

theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
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
                      Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                        Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                          Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                            Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                              emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
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

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact v23 shell
sufficient for any current replacement-positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair
    :
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
          ∀ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset sharedInteriorPairAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
    h sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      sharedInteriorPairTaitEdgeColoring
      sharedInteriorPairTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_sharedInteriorPair
      red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1)
      nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with simultaneous failure of every current replacement-positive endpoint already refutes
a universal derivation of that direct-or-route-facing positive disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                        Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                          Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                            Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23, hHeight, hCollar, hClosedWalk, hSuccessorCycle⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23 with
    hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

end Theorem49ResidualBoundaryObstruction

end Mettapedia.GraphTheory.FourColor
