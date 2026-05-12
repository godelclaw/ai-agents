import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ForcingInteriorEdgeObstructionRegression

open Theorem49InteriorVerticesEndpointObstruction
open Theorem49ForcingInteriorEdgeObstruction
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-- The diamond-with-triangle calibration of the abstract forcing-edge witness. -/
def diamondWithTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness diamondWithTriangleEmbedding where
  edge := dt12
  heInterior := dt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf

/-- The named positive non-forcing condition fails on the diamond-with-triangle model. -/
theorem not_everyInteriorEdgeHasBoundaryFreeIncidentFace_diamondWithTriangle :
    ¬ EveryInteriorEdgeHasBoundaryFreeIncidentFace diamondWithTriangleEmbedding := by
  intro hfree
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      hfree ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩

/-- The diamond-with-triangle model also cannot carry the selector form of the positive
non-forcing condition. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_diamondWithTriangle :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector diamondWithTriangleEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩

/-- The diamond-with-triangle embedding satisfies the exact face-local hypothesis used by the
failed forcing-edge exclusion attempt: each face has at most one interior boundary edge. -/
theorem diamondWithTriangle_atMostOneInteriorEdgePerFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces)).card ≤ 1 := by
  intro f
  rw [diamondWithTriangle_interiorEdgeSupport_eq_singleton]
  refine Finset.card_le_one_iff.2 ?_
  intro e e' he he'
  have he12 : e = dt12 := by
    simpa using (Finset.mem_filter.1 he).2
  have he'12 : e' = dt12 := by
    simpa using (Finset.mem_filter.1 he').2
  exact he12.trans he'12.symm

/-- The diamond-with-triangle embedding carries boundary reachability, honest closed walks, the
at-most-one-interior-edge-per-face condition, and a forcing interior-edge witness on the same
embedding. -/
theorem
    exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ _ : PlanarBoundaryClosedWalkEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
            Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleClosedWalkEmbeddingData,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- Consequently, the proposed universal forcing-edge exclusion theorem with reachability,
closed-walk embedding data, and at-most-one interior edge per face is false. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        PlanarBoundaryAnnulusBoundaryReachabilityData emb →
          PlanarBoundaryClosedWalkEmbeddingData emb →
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
              ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

/-- The chained-diamonds benchmark has genuine interior support: the two diamond diagonals
`cdt12` and `cdt45` are both interior edges. -/
theorem chainedDiamondsWithTriangle_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces).Nonempty := by
  exact ⟨cdt12, cdt12_mem_interiorEdgeSupport⟩

theorem exists_selectedBoundarySupport_of_cdt12_mem_faceBoundary_chainedDiamondsWithTriangle
    {f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces}
    (hf : cdt12 ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1) :
    ∃ b ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1,
      b ∈ selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  obtain ⟨⟨i, hi⟩, hfmem⟩ := f
  interval_cases i
  · refine ⟨cdt02, ?_, cdt02_mem_selectedBoundarySupport⟩
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary]
  · refine ⟨cdt13, ?_, cdt13_mem_selectedBoundarySupport⟩
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary]
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt35, cdt34, cdt45] at hf
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt56, cdt46, cdt45] at hf
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt78, cdt89, cdt97] at hf

/-- The first chained-diamond interior edge is forcing: every face incident to it already
contains selected-boundary support. -/
def chainedDiamondsWithTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness chainedDiamondsWithTriangleEmbedding where
  edge := cdt12
  heInterior := cdt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_cdt12_mem_faceBoundary_chainedDiamondsWithTriangle hf

/-- Direct exercise of the source-fixed raw-cover parent constructor on a nondegenerate honest
benchmark.  If the canonical closed-walk source on the chained-diamonds graph satisfied the raw
canonical-parent cover premises, the constructor would produce parent peel data; the concrete
forcing interior edge `cdt12` rules that data out. -/
theorem false_of_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    (peelFaces : Finset (AmbientFace chainedDiamondsWithTriangleEmbedding.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces)
    (hcoverRoots : RootSetCovers
      (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces)
      chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated
      (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces)
      chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (chainedDiamondsWithTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsWithTriangleEmbedding.faces))
    (hcover : interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique
        chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces hunique
        (interiorDualSpanningForestRoot chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots
          hcoverRoots hsepRoots)
        chainedDiamondsClosedWalkAnnulusBoundarySource.fallbackEdge)) :
    False := by
  let data :=
    interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      chainedDiamondsClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots
      hsepRoots hpeelInterior hcover
  exact
    false_of_interiorDualBoundaryRootParentPeelData data
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- The nondegenerate chained-diamonds source cannot instantiate the source-fixed raw-cover
canonical-parent constructor. -/
theorem not_exists_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover :
    ¬ ∃ peelFaces : Finset (AmbientFace chainedDiamondsWithTriangleEmbedding.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
        chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
        (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces)
        chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
        (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces)
        chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (chainedDiamondsWithTriangleEmbedding.faceBoundary f.1)
            (selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
              chainedDiamondsWithTriangleEmbedding.faces
              chainedDiamondsWithTriangleEmbedding.faces)) ∧
        interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
            chainedDiamondsWithTriangleEmbedding.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique
            chainedDiamondsWithTriangleEmbedding.faceBoundary
            chainedDiamondsWithTriangleEmbedding.faces hunique
            (interiorDualSpanningForestRoot chainedDiamondsWithTriangleEmbedding.faceBoundary
              chainedDiamondsWithTriangleEmbedding.faces
              chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots
              hcoverRoots hsepRoots)
            chainedDiamondsClosedWalkAnnulusBoundarySource.fallbackEdge) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    false_of_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
      diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
      diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
honest closed-walk source level. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The same diamond-with-triangle embedding simultaneously carries the honest closed-walk source,
the stronger cyclic face-arc shell derived from it, and the forcing interior-edge witness. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The same embedding also carries the weaker bundled selected-boundary-arc shell together with
the honest source and forcing interior-edge witness. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
cyclic ordered face-arc level. -/
theorem
    exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
weaker selected-boundary-arc level. -/
theorem
    exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- No embedding of the same graph can simultaneously carry the honest closed-walk annulus
source, the forcing interior-edge witness, and the peeled interior-dual package. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_interiorDualBoundaryRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, cyclic ordered
face arcs, the forcing interior-edge witness, and the reduced positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, bundled
selected-boundary arc geometry, the forcing interior-edge witness, and the reduced
positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, bundled
selected-boundary arc geometry, the forcing interior-edge witness, and the reduced
positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

/-- Route implication of the diamond-with-triangle benchmark: the honest source and repaired
previous-boundary witness lanes can already be inhabited while the interior-dual root-distance
packages are impossible on the same embedding.  This records that the interior-dual
adjacency-distance route is a sufficient upstream construction, not a consequence of the
source-plus-previous-boundary geometry present in this benchmark. -/
theorem
    diamondWithTriangle_source_previousBoundaryWitness_and_witnessCover_without_interiorDual_rootDistance :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (ForcingInteriorEdgeWitness diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- Failed converse form: repaired previous-boundary witness geometry alone cannot be used to
derive the current interior-dual root-distance package. -/
theorem
    not_forall_interiorDualBoundaryRootAdjDistancePeelData_of_previousBoundaryWitnessGeometry_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  intro h
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness
    (h (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩)

/-- Failed route-facing converse: even honest closed-walk source data plus repaired
previous-boundary witness geometry does not force the two-sided annulus-root
adjacency-distance package. -/
theorem
    not_forall_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness
    (h (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

/-- The wheel-with-inner-triangle benchmark has a forcing interior edge at the central spoke
`wit01`: every face incident to that spoke also contains selected boundary support. -/
def wheelWithInnerTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness wheelWithInnerTriangleEmbedding where
  edge := wit01
  heInterior := wit01_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    rcases f with ⟨face, _hface⟩
    change WheelWithInnerTriangleFace at face
    fin_cases face
    · refine ⟨wit12, ?_, wit12_mem_selectedBoundarySupport⟩
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
    · exfalso
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit23] at hf
    · refine ⟨wit31, ?_, wit31_mem_selectedBoundarySupport⟩
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
    · exfalso
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wheelWithInnerTriangleGraph, wit01, wit45, wit56, wit64] at hf

theorem nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle :
    Nonempty (ForcingInteriorEdgeWitness wheelWithInnerTriangleEmbedding) :=
  ⟨wheelWithInnerTriangleForcingInteriorEdgeWitness⟩

/-- The wheel benchmark fails the positive local no-forcing condition: the central spoke has no
incident face whose boundary avoids selected-boundary support. -/
theorem not_everyInteriorEdgeHasBoundaryFreeIncidentFace_wheelWithInnerTriangle :
    ¬ EveryInteriorEdgeHasBoundaryFreeIncidentFace wheelWithInnerTriangleEmbedding := by
  intro hfree
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      hfree nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle

/-- Hence the wheel benchmark cannot carry a boundary-free incident-face selector.  This keeps
the selector route honest on the same source-bearing, Tait-colorable obstruction used by the
height-cycle regressions. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

/-- Every face in the wheel-with-inner-triangle benchmark is represented by a three-edge
boundary. -/
theorem wheelWithInnerTriangleFaceBoundary_card_eq_three
    (f : WheelWithInnerTriangleFace) :
    (wheelWithInnerTriangleEmbedding.faceBoundary f).card = 3 := by
  fin_cases f <;> decide

theorem wheelWithInnerTriangle_faceBoundary_card_eq_three
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    (wheelWithInnerTriangleEmbedding.faceBoundary f.1).card = 3 := by
  exact wheelWithInnerTriangleFaceBoundary_card_eq_three f.1

theorem wheelWithInnerTriangle_two_le_faceBoundary_card
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    2 ≤ (wheelWithInnerTriangleEmbedding.faceBoundary f.1).card := by
  rw [wheelWithInnerTriangle_faceBoundary_card_eq_three f]
  decide

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_mem_interiorEdgeSupport_of_forall_face_two_le_faceBoundary_card
      (emb := wheelWithInnerTriangleEmbedding)
      wit01_mem_interiorEdgeSupport
      wheelWithInnerTriangle_two_le_faceBoundary_card

theorem hasUnblockedInteriorEndpoint_wheelWithInnerTriangle :
    HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding := by
  exact
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      wheelWithInnerTriangleEmbedding).2
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle

/-- Concrete source-to-Theorem 4.9 bridge on the wheel benchmark.  If the same wheel embedding
could supply the generic IDBRAD datum, the already-formalized closed-walk source, live endpoint,
and Tait coloring would reach the projected Theorem 4.9 synthesis endpoint. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring := by
  rcases nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource with ⟨source⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait

/-- Concrete raw Definition 4.8 quotient/error endpoint obtained from the same wheel-level
source-to-Theorem 4.9 bridge. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRawQuotientErrorPackage_of_interiorDualBoundaryRootAdjDistancePeelData
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary)
    {x : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule wheelWithInnerTriangleGraph
      (selectedBoundaryInteriorEdgeEndpointVertices wheelWithInnerTriangleEmbedding)) :
    Theorem49BoundaryRawQuotientErrorPackage wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring x := by
  rcases nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource with ⟨source⟩
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source interiorData hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait hx

/-- On the wheel benchmark, the conditional source-to-Theorem 4.9 bridge and the terminal-card
IDBRAD obstruction meet on the same hypothetical datum. -/
theorem wheelWithInnerTriangle_source_to_theorem49_and_terminal_card_contradiction_of_interiorDualBoundaryRootAdjDistancePeelData
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleTaitEdgeColoring ∧
      False := by
  exact
    ⟨wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData
        interiorData,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound
        ⟨interiorData⟩⟩

/-- The closed-walk source, a hypothetical same-embedding IDBRAD datum, and the downstream
projected Theorem 4.9 endpoint cannot coexist on the wheel benchmark.  This is the concrete
failure of the current source-to-IDBRAD route, stated at the endpoint it is meant to feed. -/
theorem not_exists_wheelWithInnerTriangle_closedWalkSource_and_interiorDualBoundaryRootAdjDistancePeelData_and_theorem49BoundaryRootNonemptyProjectedSynthesis :
    ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding,
        ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary,
          Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
            wheelWithInnerTriangleTaitEdgeColoring := by
  rintro ⟨_source, interiorData, _hProjected⟩
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound
      ⟨interiorData⟩

/-- Source-facing package at the projected endpoint: the wheel has the honest source, Tait
coloring, and unblocked endpoint, but no same-embedding IDBRAD-based projected Theorem 4.9
instantiation. -/
theorem wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_based_projectedSynthesis :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
      ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource
            wheelWithInnerTriangleEmbedding,
          ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData
            wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary,
            Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
              wheelWithInnerTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_exists_wheelWithInnerTriangle_closedWalkSource_and_interiorDualBoundaryRootAdjDistancePeelData_and_theorem49BoundaryRootNonemptyProjectedSynthesis⟩

/-- Concrete source-to-Theorem 4.9 bridge for the source-fixed canonical-parent route on the
wheel benchmark.  This instantiates the new closed-walk-source theorem without adding another
abstract package layer: the only remaining assumptions are the concrete wheel embedding's
source-boundary roots, rooted shared-edge cover, and canonical parent child-membership data. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    (source :
      PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding)
    (peelFaces : Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges
      wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces)
    (hcoverRoots : RootSetCovers
      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated
      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces))
    (hcover : interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces hunique
        (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈
        (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique
            wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces
            hunique
            (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge f),
      e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot
              (interiorDualSpanningForest wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces)
              (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
      wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait

/-- On the wheel benchmark, the concrete source-fixed canonical-parent hypotheses that feed the
new source-to-projected-Theorem-4.9 bridge already lower to height-ordered witness-cover data.
The known three-spoke height cycle rules that data out, so the instantiated source theorem does
not accidentally fire from the wheel's honest source, Tait coloring, and live carrier alone. -/
theorem wheelWithInnerTriangle_source_to_theorem49_and_height_cycle_contradiction_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    (source :
      PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding)
    (peelFaces : Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges
      wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces)
    (hcoverRoots : RootSetCovers
      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated
      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces))
    (hcover : interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces hunique
        (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈
        (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique
            wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces
            hunique
            (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge f),
      e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot
              (interiorDualSpanningForest wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces)
              (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleTaitEdgeColoring ∧
      False := by
  let parentData :=
    interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
  have hHeight :
      PlanarBoundaryHeightOrderedFacePeelWitnessData
        wheelWithInnerTriangleEmbedding :=
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
      parentData.toInteriorDualHeightParentPeelData
  exact
    ⟨wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        ⟨hHeight⟩⟩

/-- The source-fixed canonical-parent route cannot be instantiated on the wheel benchmark.  This
is the concrete endpoint-level soundness check for the new closed-walk-source-to-projected
Theorem 4.9 bridge. -/
theorem not_exists_wheelWithInnerTriangle_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_theorem49BoundaryRootNonemptyProjectedSynthesis :
    ¬ ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        ∃ peelFaces : Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
        ∃ hunique : PairwiseUniqueSharedInteriorEdges
          wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces,
        ∃ hcoverRoots : RootSetCovers
          (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces)
          source.boundaryFaceRoots,
        ∃ hsepRoots : RootSetSeparated
          (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces)
          source.boundaryFaceRoots,
          (∀ f ∈ peelFaces,
            Disjoint (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
              (selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces
                wheelWithInnerTriangleEmbedding.faces)) ∧
          interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
            (rootedSharedInteriorEdgeOfPairwiseUnique
              wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces hunique
              (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                hcoverRoots hsepRoots)
              source.fallbackEdge) ∧
          (∀ f ∈ peelFaces, ∀ e ∈
              (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
                (rootedSharedInteriorEdgeOfPairwiseUnique
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces hunique
                  (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                    hcoverRoots hsepRoots)
                  source.fallbackEdge f),
            e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces ∨
              ∃ g ∈ peelFaces,
                parentTowardsRoot
                    (interiorDualSpanningForest wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    (interiorDualSpanningForestRoot
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                      hcoverRoots hsepRoots) g = some f ∧
                e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) ∧
          Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
            wheelWithInnerTriangleTaitEdgeColoring := by
  rintro
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hchildren, _hProjected⟩
  exact
    (wheelWithInnerTriangle_source_to_theorem49_and_height_cycle_contradiction_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren).2

/-- Source-facing summary for the parent route on the wheel benchmark: the concrete graph has an
honest source, a Tait coloring, and an unblocked endpoint, but the source-fixed canonical-parent
Theorem 4.9 instantiation is blocked by the same height-cycle obstruction. -/
theorem wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_boundaryFaceRootsCanonicalParent_based_projectedSynthesis :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
      ¬ ∃ source :
            PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
          ∃ peelFaces : Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
          ∃ hunique : PairwiseUniqueSharedInteriorEdges
            wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces,
          ∃ hcoverRoots : RootSetCovers
            (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces)
            source.boundaryFaceRoots,
          ∃ hsepRoots : RootSetSeparated
            (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces)
            source.boundaryFaceRoots,
            (∀ f ∈ peelFaces,
              Disjoint (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                (selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces)) ∧
            interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
              (rootedSharedInteriorEdgeOfPairwiseUnique
                wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces hunique
                (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                  hcoverRoots hsepRoots)
                source.fallbackEdge) ∧
            (∀ f ∈ peelFaces, ∀ e ∈
                (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces hunique
                    (interiorDualSpanningForestRoot wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                      hcoverRoots hsepRoots)
                    source.fallbackEdge f),
              e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces
                    wheelWithInnerTriangleEmbedding.faces ∨
                ∃ g ∈ peelFaces,
                  parentTowardsRoot
                      (interiorDualSpanningForest wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (interiorDualSpanningForestRoot
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces source.boundaryFaceRoots
                        hcoverRoots hsepRoots) g = some f ∧
                  e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) ∧
            Theorem49BoundaryRootNonemptyProjectedSynthesis wheelWithInnerTriangleEmbedding
              wheelWithInnerTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_exists_wheelWithInnerTriangle_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_theorem49BoundaryRootNonemptyProjectedSynthesis⟩

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData wheelWithInnerTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

/-- Exact Step~2 residual seed on a live wheel face of the nondegenerate source benchmark. -/
theorem nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary :
    Nonempty
      (V23ResidualBoundaryInitialState wheelWithInnerTriangleTaitEdgeColoring red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)) := by
  exact
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      wheelWithInnerTriangleTaitEdgeColoring red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)⟩

theorem not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle :
    ¬ Nonempty
      (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
        wheelWithInnerTriangleEmbedding) := by
  intro hResidual
  exact
    not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
      ((nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_iff_nonempty_planarBoundaryCollarLayerFacePeelWitnessData).1
        hResidual)

theorem not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle :
    ¬ Nonempty (ResidualBoundarySelectorData wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        data hasUnblockedInteriorEndpoint_wheelWithInnerTriangle)

/-- Exact-v23 calibration on the nondegenerate wheel benchmark: even after adding the algebraic
Step~2 seed to the honest source, concrete Tait coloring, and live purified carrier, none of the
current residual same-embedding witness packages becomes available. -/
theorem
    wheelWithInnerTriangle_closedWalkSource_tait_nonempty_carrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry
    :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      Nonempty
        (V23ResidualBoundaryInitialState wheelWithInnerTriangleTaitEdgeColoring red blue
          (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)) ∧
      ¬ Nonempty
        (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (ResidualBoundarySelectorData wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle⟩

/-- The exact v23 seed still does not repair the natural residual same-embedding witness surfaces
on the live wheel carrier benchmark. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases h wheelWithInnerTriangleEmbedding
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      wheelWithInnerTriangleTaitEdgeColoring
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary with
    hResidual | hSelector | hHeight | hCollar
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle hSelector
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle⟩

theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      wheelWithInnerTriangleDartSuccessorCycleGeometry
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      wheelWithInnerTriangleTaitEdgeColoring
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary with
    hResidual | hSelector | hHeight | hCollar
  · exact
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle
        hResidual
  · exact not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle hSelector
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar

/-- The wheel benchmark combines the positive coloring/carrier facts with a forcing-edge
obstruction to the current annulus-root and face-layer construction routes. -/
theorem
    wheelWithInnerTriangle_tait_nonempty_carrier_and_forcing_obstruction :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      Nonempty (ForcingInteriorEdgeWitness wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- The wheel benchmark has the source, coloring, and local endpoint ingredients needed by the
raw source-IDBRAD bridge, but the same embedding cannot supply the generic IDBRAD datum.  Thus
the failure is pinned on the source-side interior-dual/witness-cover construction, not on a
vacuous carrier or absent Tait coloring. -/
theorem wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- The same source bridge obstruction can be obtained directly from the terminal-card criterion:
the source has only three-edge face boundaries, while IDBRAD would force a peeled face of boundary
cardinality at most one. -/
theorem wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_via_terminal_card :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound⟩

/-- Source-bearing selector calibration: the wheel benchmark has the honest closed-walk source,
Tait coloring, and nonempty purified carrier, but it still has no boundary-free selector and no
current acyclic witness-cover or weak annulus-collar endpoint on the same embedding. -/
theorem wheelWithInnerTriangle_closedWalkSource_tait_nonempty_carrier_without_selector_or_acyclicEndpoint :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Nonempty
        (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Even after adding the boundary-free selector alternative, honest closed-walk annulus source
data, Tait colorability, and a nonempty purified carrier do not universally construct any current
same-embedding selector or acyclic annulus endpoint.  The wheel benchmark supplies the
counterexample. -/
theorem not_forall_some_boundaryFreeSelector_or_acyclicEndpoint_of_closedWalkSource_tait_carrier_wheel :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (BoundaryFreeIncidentFaceSelector emb) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                    Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rcases hAny with hSelector | hWellFounded | hHeight | hCollar | hAnnulus
  · exact not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle hSelector
  · exact
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
        hWellFounded
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
  · exact
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
        hAnnulus

end Theorem49ForcingInteriorEdgeObstructionRegression

end Mettapedia.GraphTheory.FourColor
