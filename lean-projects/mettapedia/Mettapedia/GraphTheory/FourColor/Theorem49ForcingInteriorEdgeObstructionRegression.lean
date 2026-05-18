import Mathlib.Data.List.TakeWhile
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryDegenerateCertificate
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

/-- The same forcing edge on the chained-diamonds honest-source benchmark already blocks the
generic boundary-root adjacency-distance interior-dual package itself. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      chainedDiamondsWithTriangleEmbedding.faces
      chainedDiamondsWithTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := chainedDiamondsWithTriangleEmbedding)
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- So the chained-diamonds honest closed-walk source inhabits the stronger local at-most-one
source package, but still does not force generic boundary-root adjacency-distance data. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_without_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangleGraph :
    (∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      ¬ Nonempty
        (InteriorDualBoundaryRootAdjDistancePeelData
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- There is no theorem deriving generic boundary-root adjacency-distance interior-dual data
from the stronger honest closed-walk source plus at-most-one-interior-edge local package, even
on the fixed chained-diamonds benchmark. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) →
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) →
          (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
            e ∈ emb.faceBoundary f.1 →
              e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
              e ∈
                source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                  source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) →
          Nonempty
            (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  intro h
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness
      (h chainedDiamondsWithTriangleEmbedding
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsCanonicalWitnessEdge
        chainedDiamondsCanonicalWitnessEdge_mem
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
        chainedDiamonds_nonInteriorOnAmbient)

/-- The same forcing edge on the chained-diamonds honest-source benchmark also blocks the current
source-facing parent-oriented annulus-root package. -/
theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData chainedDiamondsWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := chainedDiamondsWithTriangleEmbedding)
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- So even the stronger chained-diamonds honest-source local package does not force the current
parent-oriented annulus-root target on the same embedding. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_without_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsCanonicalWitnessEdge, ?_⟩
  exact
    ⟨chainedDiamondsCanonicalWitnessEdge_mem,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      chainedDiamonds_nonInteriorOnAmbient,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- There is no theorem deriving the current parent-oriented annulus-root target from the stronger
honest closed-walk source plus at-most-one-interior-edge local package, even on the fixed
chained-diamonds benchmark. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) →
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) →
          (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
            e ∈ emb.faceBoundary f.1 →
              e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
              e ∈
                source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                  source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) →
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness
      (h chainedDiamondsWithTriangleEmbedding
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsCanonicalWitnessEdge
        chainedDiamondsCanonicalWitnessEdge_mem
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
        chainedDiamonds_nonInteriorOnAmbient)

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

/-- The genuine cyclic diamond benchmark already carries the final theorem-4.9 synthesis
endpoint under its explicit Tait coloring while still exhibiting a forcing interior edge. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      (∃ C : diamondWithTriangleGraph.EdgeColoring Color,
        IsTaitEdgeColoring diamondWithTriangleGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleTaitEdgeColoring,
        diamondWithTriangleTaitEdgeColoring_isTait,
        diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring⟩,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- So even the final theorem-4.9 synthesis endpoint under an actual Tait coloring does not
universally force the weaker same-embedding annulus-root adjacency-distance package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph}
        (C : diamondWithTriangleGraph.EdgeColoring Color),
        IsTaitEdgeColoring diamondWithTriangleGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

/-- So even the final theorem-4.9 synthesis endpoint under an actual Tait coloring does not
universally force the stronger same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph}
        (C : diamondWithTriangleGraph.EdgeColoring Color),
        IsTaitEdgeColoring diamondWithTriangleGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

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

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
      wheelWithInnerTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
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

/-- Even after adding exact one-collar current-boundary data, the exact-v23 live-carrier wheel
benchmark still fails every current natural residual same-embedding witness package on the honest
closed-walk source shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
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
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
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

/-- Exact one-collar current-boundary data still does not make the honest closed-walk exact-v23
live-carrier shell sufficient for any current natural residual same-embedding witness package on
the wheel benchmark. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
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
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk shell
together with simultaneous failure of every current natural residual same-embedding endpoint
already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
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
                (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hResidual, hSelector,
      hHeight, hCollar⟩
  rcases h emb source hcurrent C hC hCarrier a b faceBoundary hv23 with hResidual' | hRest
  · exact hResidual hResidual'
  · rcases hRest with hSelector' | hRest
    · exact hSelector hSelector'
    · rcases hRest with hHeight' | hCollar'
      · exact hHeight hHeight'
      · exact hCollar hCollar'

/-- The same exact one-collar current-boundary refinement still does not force any current
natural residual same-embedding witness package on the actual successor-cycle boundary-order shell
of the exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
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
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
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

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier shell sufficient for any current natural residual same-embedding witness package on
the wheel benchmark. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
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
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  rcases h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      wheelWithInnerTriangleDartSuccessorCycleGeometry
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
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

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with simultaneous failure of every current natural residual same-embedding endpoint
already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                        Nonempty (ResidualBoundarySelectorData emb) ∨
                        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hResidual, hSelector, hHeight, hCollar⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b faceBoundary hv23 with
    hResidual' | hRest
  · exact hResidual hResidual'
  · rcases hRest with hSelector' | hRest
    · exact hSelector hSelector'
    · rcases hRest with hHeight' | hCollar'
      · exact hHeight hHeight'
      · exact hCollar hCollar'

/-- Even after upgrading the live exact-v23 one-collar natural-residual wheel shell to a genuine
unblocked interior endpoint, the same embedding still fails every current natural residual
same-embedding witness package on the honest closed-walk source shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
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
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hResidual, hSelector,
      hHeight, hCollar⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩

/-- The named unblocked endpoint still does not make the honest closed-walk exact-v23 one-collar
wheel shell sufficient for any current natural residual same-embedding witness package. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
                HasUnblockedInteriorEndpoint emb →
                  ∀ a b : Color,
                    ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                      Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                        Nonempty (ResidualBoundarySelectorData emb) ∨
                        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  exact
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
      (by
        intro emb source hcurrent C hC hnonempty a b faceBoundary hv23
        exact
          h emb source hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with simultaneous failure of every current natural residual
same-embedding endpoint already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
  exact
    (not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hResidual,
            hSelector, hHeight, hCollar⟩
        exact
          ⟨emb, source, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩)
      (by
        intro emb source hcurrent C hC hnonempty a b faceBoundary hv23
        exact
          h emb source hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23))

/-- Even after upgrading the live exact-v23 one-collar natural-residual wheel shell to a genuine
unblocked interior endpoint, the same embedding still fails every current natural residual
same-embedding witness package on the actual successor-cycle boundary-order shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
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
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hResidual, hSelector, hHeight, hCollar⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩

/-- The named unblocked endpoint still does not make the successor-cycle exact-v23 one-collar
wheel shell sufficient for any current natural residual same-embedding witness package. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  exact
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with simultaneous failure of every current natural residual
same-embedding endpoint already refutes a universal derivation of that natural residual burden. -/
theorem
    not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
  refine
    (not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩
    exact
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hResidual, hSelector, hHeight, hCollar⟩
  · intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
      hv23
    exact
      h emb boundaryData dartCycles hboundaryArc hcurrent C hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        a b faceBoundary hv23

/-- The wheel benchmark also blocks the closed-walk route-facing annulus-collar replacement
package, since that package lowers to the direct collar-layer replacement surface. -/
theorem not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
      wheelWithInnerTriangleEmbedding := by
  intro geom
  exact
    not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- The same fixed-embedding obstruction blocks the successor-cycle route-facing annulus-collar
replacement package as well. -/
theorem not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
      wheelWithInnerTriangleEmbedding := by
  intro geom
  exact
    not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- Even with the exact v23 residual seed present, the live-carrier wheel benchmark still does
not realize any current direct or route-facing replacement-positive package on the same
embedding. -/
theorem
    wheelWithInnerTriangle_closedWalkSource_tait_nonempty_carrier_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn
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
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data still does not upgrade the honest-source exact-v23
live-carrier wheel shell into any current direct or route-facing replacement-positive package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact-v23
live-carrier wheel shell sufficient for any current direct or route-facing replacement-positive
package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hSuccessorCycle

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk shell
together with simultaneous failure of every current replacement-positive endpoint already refutes
a universal derivation of that direct-or-route-facing positive disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                        Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                        Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                        Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hHeight, hCollar,
      hClosedWalk, hSuccessorCycle⟩
  rcases h emb source hcurrent C hC hCarrier a b faceBoundary hv23 with hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

/-- The same exact one-collar refinement still does not force any current direct or route-facing
replacement-positive package on the actual successor-cycle boundary-order shell of the exact-v23
live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Joint obstruction on the actual successor-cycle exact-v23 wheel shell: the same fixed
embedding already carries a concrete face boundary with two distinct interior edges while still
failing every currently formalized direct or route-facing replacement-positive package.  This
records the upstream positive obstruction directly on the benchmark geometry itself. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier wheel shell sufficient for any current direct or route-facing replacement-positive
package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      wheelWithInnerTriangleDartSuccessorCycleGeometry
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hSuccessorCycle

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with simultaneous failure of every current replacement-positive endpoint already refutes
a universal derivation of that direct-or-route-facing positive disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                        Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                        Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                        Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hHeight, hCollar, hClosedWalk, hSuccessorCycle⟩
  rcases h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b faceBoundary hv23 with
    hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

/-- Even after upgrading the live honest exact-v23 wheel shell to a genuine unblocked interior
endpoint, the same embedding still fails every currently formalized direct or route-facing
replacement-positive package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Adding an actual unblocked interior endpoint still does not make the live honest exact-v23
one-collar wheel shell sufficient for any current direct or route-facing replacement-positive
package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hSuccessorCycle

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with simultaneous failure of every current replacement-positive
endpoint already refutes a universal derivation of that direct-or-route-facing positive
disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

/-- Even after upgrading the live successor-cycle exact-v23 wheel shell to a genuine unblocked
interior endpoint, the same embedding still carries a concrete two-interior-edge face boundary
while failing every currently formalized direct or route-facing replacement-positive package. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Adding an actual unblocked interior endpoint still does not make the live successor-cycle
exact-v23 one-collar wheel shell sufficient for any current direct or route-facing
replacement-positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      wheelWithInnerTriangleDartSuccessorCycleGeometry
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle
            hSuccessorCycle

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with simultaneous failure of every current
replacement-positive endpoint already refutes a universal derivation of that direct-or-route-
facing positive disjunction. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23, hHeight, hCollar, hClosedWalk, hSuccessorCycle⟩
  rcases h emb boundaryData dartCycles C a b faceBoundary hboundaryArc hcurrent hC hEndpoint hv23 with
    hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hClosedWalk' | hSuccessorCycle'
      · exact hClosedWalk hClosedWalk'
      · exact hSuccessorCycle hSuccessorCycle'

/-- The raw attached-face certificate is also impossible on the fixed wheel embedding.  Any
first peeled face whose witness is one of the three interior spokes must have another interior
spoke on the same triangular boundary, but that companion spoke lies neither on selected-boundary
support nor among earlier witness edges by minimality. -/
theorem
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle :
    ¬ Nonempty
        (BoundaryRootedFacePeelCertificate
          wheelWithInnerTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := wheelWithInnerTriangleEmbedding.faces)
            wheelWithInnerTriangleEmbedding.faceBoundary)) := by
  rintro ⟨cert⟩
  let subBoundary : AmbientFace wheelWithInnerTriangleEmbedding.faces →
      Finset wheelWithInnerTriangleGraph.edgeSet :=
    ambientFaceBoundary (allFaces := wheelWithInnerTriangleEmbedding.faces)
      wheelWithInnerTriangleEmbedding.faceBoundary
  let base : Finset wheelWithInnerTriangleGraph.edgeSet :=
    selectedBoundarySupport subBoundary
      wheelWithInnerTriangleEmbedding.faces.attach
      wheelWithInnerTriangleEmbedding.faces.attach
  have hbase01 : wit01 ∉ base := by
    intro h
    exact wit01_not_mem_selectedBoundarySupport (by
      simpa [base, subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
        (allFaces := wheelWithInnerTriangleEmbedding.faces)] using h)
  have hbase02 : wit02 ∉ base := by
    intro h
    exact wit02_not_mem_selectedBoundarySupport (by
      simpa [base, subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
        (allFaces := wheelWithInnerTriangleEmbedding.faces)] using h)
  have hbase03 : wit03 ∉ base := by
    intro h
    exact wit03_not_mem_selectedBoundarySupport (by
      simpa [base, subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
        (allFaces := wheelWithInnerTriangleEmbedding.faces)] using h)
  set nonSpoke : AmbientFace wheelWithInnerTriangleEmbedding.faces → Bool :=
    fun f =>
      decide
        (cert.witnessEdge f ≠ wit01 ∧
          cert.witnessEdge f ≠ wit02 ∧
          cert.witnessEdge f ≠ wit03)
  set facePrefix := cert.faceOrder.takeWhile nonSpoke
  have hwit01Interior :
      wit01 ∈ interiorEdgeSupport subBoundary
        wheelWithInnerTriangleEmbedding.faces.attach := by
    simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
      (allFaces := wheelWithInnerTriangleEmbedding.faces)] using
        wit01_mem_interiorEdgeSupport
  have hwit01Support :
      wit01 ∈ facePeelWitnessSupport cert.faceOrder cert.witnessEdge :=
    cert.coverInterior hwit01Interior
  have hsuffix_ne_nil : List.dropWhile nonSpoke cert.faceOrder ≠ [] := by
    intro hsuffix
    have hsplitNil : cert.faceOrder = facePrefix := by
      have hsplit :
          facePrefix ++ List.dropWhile nonSpoke cert.faceOrder = cert.faceOrder := by
        simpa [facePrefix] using
          (List.takeWhile_append_dropWhile (p := nonSpoke) (l := cert.faceOrder))
      rw [hsuffix, List.append_nil] at hsplit
      exact hsplit.symm
    rcases (mem_facePeelWitnessSupport_iff cert.faceOrder cert.witnessEdge).1 hwit01Support with
      ⟨g, hg, hgw⟩
    have hgPrefix : g ∈ facePrefix := by
      simpa [hsplitNil] using hg
    have hgood : nonSpoke g := by
      have hgTake : g ∈ cert.faceOrder.takeWhile nonSpoke := by
        simpa [facePrefix] using hgPrefix
      exact List.mem_takeWhile_imp (p := nonSpoke) hgTake
    have hgood' :
        cert.witnessEdge g ≠ wit01 ∧
          cert.witnessEdge g ≠ wit02 ∧
          cert.witnessEdge g ≠ wit03 := by
      simpa [nonSpoke] using hgood
    exact False.elim (hgood'.1 hgw)
  cases hdrop : List.dropWhile nonSpoke cert.faceOrder with
  | nil =>
      exact False.elim (hsuffix_ne_nil hdrop)
  | cons f tail =>
      have hsplit' : facePrefix ++ List.dropWhile nonSpoke cert.faceOrder = cert.faceOrder := by
        simpa [facePrefix] using
          (List.takeWhile_append_dropWhile (p := nonSpoke) (l := cert.faceOrder))
      have hsplit : cert.faceOrder = facePrefix ++ f :: tail := by
        simpa [hdrop] using hsplit'.symm
      have hfnot : ¬ nonSpoke f := by
        have hzero :
            ¬ nonSpoke
                ((List.dropWhile nonSpoke cert.faceOrder).get
                  ⟨0, by simp [hdrop]⟩) :=
          List.dropWhile_get_zero_not (p := nonSpoke) (l := cert.faceOrder)
            (by simp [hdrop])
        simpa [hdrop] using hzero
      have hprefixGood : ∀ g ∈ facePrefix, nonSpoke g := by
        intro g hg
        exact List.mem_takeWhile_imp (p := nonSpoke) (by simpa [facePrefix] using hg)
      have hprefix01 : wit01 ∉ facePeelWitnessSupport facePrefix cert.witnessEdge := by
        intro hmem
        rcases (mem_facePeelWitnessSupport_iff facePrefix cert.witnessEdge).1 hmem with
          ⟨g, hg, hgw⟩
        have hgood' :
            cert.witnessEdge g ≠ wit01 ∧
              cert.witnessEdge g ≠ wit02 ∧
              cert.witnessEdge g ≠ wit03 := by
          simpa [nonSpoke] using hprefixGood g hg
        exact hgood'.1 hgw
      have hprefix02 : wit02 ∉ facePeelWitnessSupport facePrefix cert.witnessEdge := by
        intro hmem
        rcases (mem_facePeelWitnessSupport_iff facePrefix cert.witnessEdge).1 hmem with
          ⟨g, hg, hgw⟩
        have hgood' :
            cert.witnessEdge g ≠ wit01 ∧
              cert.witnessEdge g ≠ wit02 ∧
              cert.witnessEdge g ≠ wit03 := by
          simpa [nonSpoke] using hprefixGood g hg
        exact hgood'.2.1 hgw
      have hprefix03 : wit03 ∉ facePeelWitnessSupport facePrefix cert.witnessEdge := by
        intro hmem
        rcases (mem_facePeelWitnessSupport_iff facePrefix cert.witnessEdge).1 hmem with
          ⟨g, hg, hgw⟩
        have hgood' :
            cert.witnessEdge g ≠ wit01 ∧
              cert.witnessEdge g ≠ wit02 ∧
              cert.witnessEdge g ≠ wit03 := by
          simpa [nonSpoke] using hprefixGood g hg
        exact hgood'.2.2 hgw
      have hfSpoke :
          cert.witnessEdge f = wit01 ∨
            cert.witnessEdge f = wit02 ∨
            cert.witnessEdge f = wit03 := by
        by_cases hw01 : cert.witnessEdge f = wit01
        · exact Or.inl hw01
        · by_cases hw02 : cert.witnessEdge f = wit02
          · exact Or.inr (Or.inl hw02)
          · by_cases hw03 : cert.witnessEdge f = wit03
            · exact Or.inr (Or.inr hw03)
            · exact False.elim (hfnot (by simp [nonSpoke, hw01, hw02, hw03]))
      rcases cert.step facePrefix tail f hsplit with ⟨hwit, hrest⟩
      rcases hfSpoke with hw01 | hw02 | hw03
      · have hwit01_f :
            wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
          simpa [subBoundary, ambientFaceBoundary, hw01] using hwit
        rcases (wit01_mem_faceBoundary_iff f).1 hwit01_f with hf0 | hf2
        · have hwit02_f :
              wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf0]
            decide
          have hwit02_sub : wit02 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit02_f
          have hwit02_erase :
              wit02 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit02_sub⟩
            intro h
            exact wit01_ne_wit02 (hw01.symm.trans h.symm)
          rcases Finset.mem_union.1 (hrest hwit02_erase) with hbase | hprev
          · exact hbase02 hbase
          · exact hprefix02 hprev
        · have hwit03_f :
              wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf2]
            decide
          have hwit03_sub : wit03 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit03_f
          have hwit03_erase :
              wit03 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit03_sub⟩
            intro h
            exact wit01_ne_wit03 (hw01.symm.trans h.symm)
          rcases Finset.mem_union.1 (hrest hwit03_erase) with hbase | hprev
          · exact hbase03 hbase
          · exact hprefix03 hprev
      · have hwit02_f :
            wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
          simpa [subBoundary, ambientFaceBoundary, hw02] using hwit
        rcases (wit02_mem_faceBoundary_iff f).1 hwit02_f with hf0 | hf1
        · have hwit01_f :
              wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf0]
            decide
          have hwit01_sub : wit01 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit01_f
          have hwit01_erase :
              wit01 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit01_sub⟩
            intro h
            exact wit01_ne_wit02 (h.trans hw02)
          rcases Finset.mem_union.1 (hrest hwit01_erase) with hbase | hprev
          · exact hbase01 hbase
          · exact hprefix01 hprev
        · have hwit03_f :
              wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf1]
            decide
          have hwit03_sub : wit03 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit03_f
          have hwit03_erase :
              wit03 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit03_sub⟩
            intro h
            exact wit02_ne_wit03 (hw02.symm.trans h.symm)
          rcases Finset.mem_union.1 (hrest hwit03_erase) with hbase | hprev
          · exact hbase03 hbase
          · exact hprefix03 hprev
      · have hwit03_f :
            wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
          simpa [subBoundary, ambientFaceBoundary, hw03] using hwit
        rcases (wit03_mem_faceBoundary_iff f).1 hwit03_f with hf1 | hf2
        · have hwit02_f :
              wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf1]
            decide
          have hwit02_sub : wit02 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit02_f
          have hwit02_erase :
              wit02 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit02_sub⟩
            intro h
            exact wit02_ne_wit03 (h.trans hw03)
          rcases Finset.mem_union.1 (hrest hwit02_erase) with hbase | hprev
          · exact hbase02 hbase
          · exact hprefix02 hprev
        · have hwit01_f :
              wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 := by
            rw [hf2]
            decide
          have hwit01_sub : wit01 ∈ subBoundary f := by
            simpa [subBoundary, ambientFaceBoundary] using hwit01_f
          have hwit01_erase :
              wit01 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
            refine Finset.mem_erase.2 ⟨?_, hwit01_sub⟩
            intro h
            exact wit01_ne_wit03 (h.trans hw03)
          rcases Finset.mem_union.1 (hrest hwit01_erase) with hbase | hprev
          · exact hbase01 hbase
          · exact hprefix01 hprev

/-- On the fixed wheel embedding, the endpoint-bearing exact-v23 successor-cycle shell has
already ruled out every current sufficient same-embedding geometric endpoint except the raw
attached peel certificate.  So any future proof of that full disjunction on this shell reduces to
producing an attached certificate on the same embedding. -/
theorem
    currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle_only_if_attachedBoundaryRootedFacePeelCertificate
    :
    (Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∨
      Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∨
      Nonempty
        (BoundaryRootedFacePeelCertificate
          wheelWithInnerTriangleEmbedding.faces.attach
          (ambientFaceBoundary
            (allFaces := wheelWithInnerTriangleEmbedding.faces)
            wheelWithInnerTriangleEmbedding.faceBoundary)) ∨
      Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∨
      Nonempty
        (PlanarBoundaryAnnulusCollarGeometry
          wheelWithInnerTriangleEmbedding)) →
      Nonempty
        (BoundaryRootedFacePeelCertificate
          wheelWithInnerTriangleEmbedding.faces.attach
          (ambientFaceBoundary
            (allFaces := wheelWithInnerTriangleEmbedding.faces)
            wheelWithInnerTriangleEmbedding.faceBoundary)) := by
  intro hAny
  rcases hAny with hHeight | hRest
  · exact False.elim
      (not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight)
  · rcases hRest with hCollar | hRest
    · exact False.elim
        (not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
          hCollar)
    · rcases hRest with hAttached | hRest
      · exact hAttached
      · rcases hRest with hWellFounded | hAnnulus
        · exact False.elim
            (not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
              hWellFounded)
        · exact False.elim
            (not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
              hAnnulus)

/-- Route-facing reduction of the endpoint-bearing exact-v23 wheel target: on the live
honest-source one-collar shell, the only remaining branch of the current sufficient
same-embedding geometry disjunction is the raw attached peel certificate on the same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_reducing_currentSufficientSameEmbeddingGeometry_to_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ((Nonempty
                      (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                    Nonempty
                      (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                    Nonempty
                      (BoundaryRootedFacePeelCertificate emb.faces.attach
                        (ambientFaceBoundary (allFaces := emb.faces)
                          emb.faceBoundary)) ∨
                    Nonempty
                      (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                    Nonempty
                      (PlanarBoundaryAnnulusCollarGeometry emb)) →
                    Nonempty
                      (BoundaryRootedFacePeelCertificate emb.faces.attach
                        (ambientFaceBoundary (allFaces := emb.faces)
                          emb.faceBoundary))) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle_only_if_attachedBoundaryRootedFacePeelCertificate⟩

/-- The remaining attached-certificate branch is also dead on the fixed wheel embedding, so the
endpoint-bearing exact-v23 honest-source shell still fails every currently sufficient
same-embedding geometry endpoint. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- The named unblocked endpoint still does not upgrade the exact one-collar current-boundary
honest-source wheel shell into any current sufficient same-embedding geometric endpoint. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                  Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
                  Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
    · rcases hRest with hAttached | hRest
      · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle
          hAttached
      · rcases hRest with hWellFounded | hAnnulus
        · exact
            not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
              hWellFounded
        · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
            hAnnulus

/-- Any explicit same-embedding witness of the endpoint-bearing exact-v23 honest closed-walk
shell carrying simultaneous failure of every currently sufficient same-embedding geometry endpoint
already refutes a universal derivation of that whole current-sufficient burden. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                  Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
                  Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hHeight, hCollar,
      hAttached, hWellFounded, hAnnulus⟩
  rcases h emb source C a b faceBoundary hcurrent hC hEndpoint hv23 with hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hAttached' | hRest
      · exact hAttached hAttached'
      · rcases hRest with hWellFounded' | hAnnulus'
        · exact hWellFounded hWellFounded'
        · exact hAnnulus hAnnulus'

/-- Route-facing reduction of the endpoint-bearing exact-v23 wheel target: on the live
successor-cycle one-collar shell, the only remaining branch of the current sufficient
same-embedding geometry disjunction is the raw attached peel certificate on the same embedding. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_reducing_currentSufficientSameEmbeddingGeometry_to_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ((Nonempty
                      (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                    Nonempty
                      (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                    Nonempty
                      (BoundaryRootedFacePeelCertificate emb.faces.attach
                        (ambientFaceBoundary (allFaces := emb.faces)
                          emb.faceBoundary)) ∨
                    Nonempty
                      (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                    Nonempty
                      (PlanarBoundaryAnnulusCollarGeometry emb)) →
                    Nonempty
                      (BoundaryRootedFacePeelCertificate emb.faces.attach
                        (ambientFaceBoundary (allFaces := emb.faces)
                          emb.faceBoundary))) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle_only_if_attachedBoundaryRootedFacePeelCertificate⟩

/-- The remaining attached-certificate branch is also dead on the fixed wheel embedding, so the
endpoint-bearing exact-v23 successor-cycle shell still fails every currently sufficient
same-embedding geometry endpoint. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- The named unblocked endpoint still does not upgrade the exact one-collar current-boundary
successor-cycle wheel shell into any current sufficient same-embedding geometric endpoint. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                  Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
                  Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      wheelWithInnerTriangleDartSuccessorCycleGeometry
      wheelWithInnerTriangleTaitEdgeColoring
      red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      hcurrent
      wheelWithInnerTriangleTaitEdgeColoring_isTait
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary
  rcases hAny with hHeight | hRest
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle hHeight
  · rcases hRest with hCollar | hRest
    · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
    · rcases hRest with hAttached | hRest
      · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle
          hAttached
      · rcases hRest with hWellFounded | hAnnulus
        · exact
            not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
              hWellFounded
        · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
            hAnnulus

/-- Any explicit same-embedding witness of the endpoint-bearing exact-v23 successor-cycle shell
carrying simultaneous failure of every currently sufficient same-embedding geometry endpoint
already refutes a universal derivation of that whole current-sufficient burden. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate emb.faces.attach
                      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
        (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
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
      hv23, hHeight, hCollar, hAttached, hWellFounded, hAnnulus⟩
  rcases h emb boundaryData dartCycles C a b faceBoundary hboundaryArc hcurrent hC hEndpoint hv23 with
    hHeight' | hRest
  · exact hHeight hHeight'
  · rcases hRest with hCollar' | hRest
    · exact hCollar hCollar'
    · rcases hRest with hAttached' | hRest
      · exact hAttached hAttached'
      · rcases hRest with hWellFounded' | hAnnulus'
        · exact hWellFounded hWellFounded'
        · exact hAnnulus hAnnulus'

/-- Even after adding exact one-collar current-boundary data, the exact-v23 honest-source
live-carrier wheel shell still does not force the downstream positive construction face-layer
package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle⟩

/-- Even after adding exact one-collar current-boundary data, the exact-v23 honest-source
live-carrier wheel shell still does not force the earliest same-embedding boundary-free
selector package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact-v23
live-carrier wheel shell sufficient for the earliest same-embedding boundary-free selector
package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hno⟩
  exact hno (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk
live-carrier shell together with failure of a boundary-free selector already refutes a universal
derivation of that earliest same-embedding selector burden. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoSelector⟩
  exact hNoSelector (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Even after adding exact one-collar current-boundary data, the exact-v23 honest-source
live-carrier wheel shell still does not force the same-embedding raw canonical-parent
shared-edge-cover package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                            source.fallbackEdge) := by
  refine
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      ?_⟩
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      (G := wheelWithInnerTriangleGraph)
      ⟨wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
        peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact-v23
live-carrier wheel shell sufficient for the same-embedding raw canonical-parent
shared-edge-cover package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hno⟩
  exact hno (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk
live-carrier shell together with failure of the raw canonical-parent shared-edge cover already
refutes a universal derivation of that source-fixed cover burden. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
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
                            source.fallbackEdge)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoCover⟩
  exact hNoCover (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the same-embedding raw
canonical-parent shared-edge-cover package on the honest exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                            source.fallbackEdge) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoCover⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoCover⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar wheel shell
sufficient for the same-embedding raw canonical-parent shared-edge-cover package. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
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
  exact
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of the raw canonical-parent shared-edge cover already
refutes a universal derivation of that source-fixed cover burden. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                            source.fallbackEdge)) :
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
  exact
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hNoCover⟩
        exact
          ⟨emb, source, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoCover⟩)
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Even after adding exact one-collar current-boundary data, the exact-v23 honest-source
live-carrier wheel shell still does not force the same-embedding annulus-root parent-peel
package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact-v23
live-carrier wheel shell sufficient for the same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := wheelWithInnerTriangleGraph)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle with
      ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23⟩
    exact h emb source C a b faceBoundary hcurrent hC hCarrier hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk
live-carrier shell together with failure of annulus-root parent-peel data already refutes a
universal derivation of that source-fixed parent-peel burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoParentPeel⟩
  exact hNoParentPeel (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the same-embedding
annulus-root parent-peel package on the honest exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoParentPeel⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoParentPeel⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar wheel shell
sufficient for the same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of annulus-root parent-peel data already refutes a
universal derivation of that source-fixed parent-peel burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) :
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
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    (not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23,
        hNoParentPeel⟩
    exact
      ⟨emb, source, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoParentPeel⟩
  · intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
    exact
      h emb source C a b faceBoundary hcurrent hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        hv23

/-- Even after adding exact one-collar current-boundary data, the exact-v23 honest-source
live-carrier wheel shell still does not force the downstream positive construction face-layer
package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Exact one-collar current-boundary data still does not make the honest-source exact-v23
live-carrier wheel shell sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := wheelWithInnerTriangleGraph)
      (P := fun emb =>
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle with
      ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hforce⟩
    exact ⟨emb, ⟨source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23⟩, hforce⟩
  · intro emb hP
    rcases hP with ⟨source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23⟩
    exact h emb source C a b faceBoundary hcurrent hC hCarrier hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk
live-carrier shell together with failure of construction face-layer data already refutes a
universal derivation of that downstream positive face-layer burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoFaceLayer⟩
  exact hNoFaceLayer (h emb source C a b faceBoundary hcurrent hC hCarrier hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the downstream positive
construction face-layer package on the honest exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoFaceLayer⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoFaceLayer⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar wheel shell
sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of construction face-layer data already refutes a
universal derivation of that downstream positive face-layer burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) :
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
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    (not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hNoFaceLayer⟩
    exact
      ⟨emb, source, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoFaceLayer⟩
  · intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
    exact
      h emb source C a b faceBoundary hcurrent hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        hv23

/-- The same exact one-collar refinement still does not force the downstream positive
construction face-layer package on the actual successor-cycle boundary-order shell of the
exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (ForcingInteriorEdgeWitness emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle⟩

/-- The same exact one-collar refinement also fails to force the earliest same-embedding
boundary-free selector package on the actual successor-cycle boundary-order shell of the
exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier wheel shell sufficient for the earliest same-embedding boundary-free selector
package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
      faceBoundary, hv23, hno⟩
  exact
    hno (h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hCarrier a b
      faceBoundary hv23)

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle
live-carrier shell together with failure of a boundary-free selector already refutes a
universal derivation of that earliest same-embedding selector burden. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) :
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoSelector⟩
  exact hNoSelector (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
    faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the earliest
same-embedding boundary-free selector package on the honest exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoSelector⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar wheel shell
sufficient for the earliest same-embedding boundary-free selector package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of a boundary-free selector already refutes a universal
derivation of that earliest same-embedding selector burden. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) :
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
                Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    (not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hNoSelector⟩
        exact
          ⟨emb, source, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoSelector⟩)
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23))

/-- Adjoining a named unblocked interior endpoint still does not force the earliest
same-embedding boundary-free selector package on the route-facing exact-v23 one-collar wheel
shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoSelector⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for the earliest same-embedding boundary-free selector package. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  refine
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      ?_
  intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary hv23
  exact
    h emb boundaryData dartCycles hboundaryArc hcurrent C hC
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hnonempty)
      a b faceBoundary hv23

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of a boundary-free selector already refutes a
universal derivation of that earliest same-embedding selector burden. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb)) :
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
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  refine
    (not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hNoSelector⟩
    exact
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoSelector⟩
  · intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
      hv23
    exact
      h emb boundaryData dartCycles hboundaryArc hcurrent C hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        a b faceBoundary hv23

/-- Exact-v23 selector wheel separation at graph-vs-fixed-embedding level: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
route-facing one-collar wheel shell with the same coloring and surviving purified carrier still
fails the earliest same-embedding boundary-free selector package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFreeIncidentFaceSelector
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨by
        refine
          ⟨allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph, ?_⟩
        letI : Inhabited wheelWithInnerTriangleGraph.edgeSet := ⟨wit01⟩
        exact
          theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
            (G := wheelWithInnerTriangleGraph)
            (degeneratePlanarBoundaryAttachedRootedFacePeelCertificate
              wheelWithInnerTriangleGraph)
            wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same exact-v23 selector wheel separation: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
one-collar wheel shell already carries an honest closed-walk source with the same surviving
purified carrier and still fails the earliest same-embedding boundary-free selector package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_boundaryFreeIncidentFaceSelector
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (BoundaryFreeIncidentFaceSelector
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFreeIncidentFaceSelector with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoSelector⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoSelector⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing graph-level selector wheel separation: the graph still admits theorem-4.9
synthesis for the explicit Tait coloring on some embedding, while the fixed route-facing
exact-v23 one-collar wheel shell already carries a real unblocked endpoint and still fails the
earliest same-embedding boundary-free selector package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector
                      wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFreeIncidentFaceSelector with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoSelector⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector⟩

/-- Honest-source reformulation of the same endpoint-bearing selector wheel separation: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with a real
unblocked endpoint and still fails the earliest same-embedding boundary-free selector package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (BoundaryFreeIncidentFaceSelector
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoSelector⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoSelector⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Exact-v23 raw canonical-parent shared-edge-cover wheel separation at graph-vs-fixed-embedding
level: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed route-facing one-collar wheel shell with the same coloring and
surviving purified carrier still fails the same-embedding raw canonical-parent cover package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFaceRootsCanonicalParentSharedEdgeCover
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
              (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
                |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
            (∃ data :
                PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
            IsTaitEdgeColoring wheelWithInnerTriangleGraph
              wheelWithInnerTriangleTaitEdgeColoring ∧
            (selectedBoundaryInteriorEdgeEndpointVertices
              wheelWithInnerTriangleEmbedding).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty
                    (V23ResidualBoundaryInitialState
                      wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                  ¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                      ∃ hunique :
                          PairwiseUniqueSharedInteriorEdges
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces,
                      ∃ hcoverRoots : RootSetCovers
                        (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      ∃ hsepRoots : RootSetSeparated
                        (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        (∀ f ∈ peelFaces,
                          Disjoint
                            (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                            (selectedBoundarySupport
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              wheelWithInnerTriangleEmbedding.faces)) ∧
                        interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces ⊆
                          peelFaces.image
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces hunique
                              (interiorDualSpanningForestRoot
                                wheelWithInnerTriangleEmbedding.faceBoundary
                                wheelWithInnerTriangleEmbedding.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  refine
    ⟨?_, wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace, ?_⟩
  · refine ⟨allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph, ?_⟩
    letI : Inhabited wheelWithInnerTriangleGraph.edgeSet := ⟨wit01⟩
    exact
      theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
        (G := wheelWithInnerTriangleGraph)
        (degeneratePlanarBoundaryAttachedRootedFacePeelCertificate
          wheelWithInnerTriangleGraph)
        wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait
  · exact
      ⟨hcurrent, wheelWithInnerTriangleTaitEdgeColoring_isTait,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
        ⟨red, blue, (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
          ⟨nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
            by
              rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
              exact
                not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
                  (G := wheelWithInnerTriangleGraph)
                  ⟨wheelWithInnerTriangleEmbedding,
                    wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
                    wheelWithInnerTriangleDartSuccessorCycleGeometry,
                    wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
                    peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
                    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩⟩⟩⟩

/-- Honest-source reformulation of the same exact-v23 raw canonical-parent wheel separation: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed one-collar wheel shell already carries an honest closed-walk source with the same
surviving purified carrier and still fails the same-embedding raw canonical-parent cover
package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_boundaryFaceRootsCanonicalParentSharedEdgeCover
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∃ peelFaces :
                  Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                  ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint
                        (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                        (selectedBoundarySupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          wheelWithInnerTriangleEmbedding.faces)) ∧
                    interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ⊆
                      peelFaces.image
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces hunique
                          (interiorDualSpanningForestRoot
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFaceRootsCanonicalParentSharedEdgeCover with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoCover⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      ?_⟩
  · simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary
  · simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields]
      using hNoCover

/-- Endpoint-bearing graph-level raw canonical-parent wheel separation: the graph still admits
theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
route-facing exact-v23 one-collar wheel shell already carries a real unblocked endpoint and
still fails the same-embedding raw canonical-parent cover package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
              (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
                |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
            (∃ data :
                PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
            IsTaitEdgeColoring wheelWithInnerTriangleGraph
              wheelWithInnerTriangleTaitEdgeColoring ∧
            HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty
                    (V23ResidualBoundaryInitialState
                      wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                  ¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                      ∃ hunique :
                          PairwiseUniqueSharedInteriorEdges
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces,
                      ∃ hcoverRoots : RootSetCovers
                        (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      ∃ hsepRoots : RootSetSeparated
                        (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                        (∀ f ∈ peelFaces,
                          Disjoint
                            (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                            (selectedBoundarySupport
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              wheelWithInnerTriangleEmbedding.faces)) ∧
                        interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces ⊆
                          peelFaces.image
                            (rootedSharedInteriorEdgeOfPairwiseUnique
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces hunique
                              (interiorDualSpanningForestRoot
                                wheelWithInnerTriangleEmbedding.faceBoundary
                                wheelWithInnerTriangleEmbedding.faces
                                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                                hcoverRoots hsepRoots)
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).fallbackEdge) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFaceRootsCanonicalParentSharedEdgeCover with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoCover⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).2 hCarrier,
      a, b, faceBoundary, hv23, hNoCover⟩

/-- Honest-source reformulation of the same endpoint-bearing raw canonical-parent wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails the same-embedding raw
canonical-parent cover package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∃ peelFaces :
                  Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                  ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint
                        (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                        (selectedBoundarySupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          wheelWithInnerTriangleEmbedding.faces)) ∧
                    interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ⊆
                      peelFaces.image
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces hunique
                          (interiorDualSpanningForestRoot
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoCover⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      ?_⟩
  · simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary
  · simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields]
      using hNoCover

/-- The same exact one-collar refinement also fails to force the same-embedding raw
canonical-parent shared-edge-cover package on the actual successor-cycle boundary-order shell of
the exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  refine
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      ?_⟩
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      (G := wheelWithInnerTriangleGraph)
      ⟨wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
        wheelWithInnerTriangleDartSuccessorCycleGeometry,
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
        peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier wheel shell sufficient for the same-embedding raw canonical-parent
shared-edge-cover package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b,
      faceBoundary, hv23, hno⟩
  exact
    hno (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
      faceBoundary hv23)

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle
live-carrier shell together with failure of the raw canonical-parent shared-edge cover already
refutes a universal derivation of that source-fixed cover burden. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoCover⟩
  exact hNoCover (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
    faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the same-embedding raw
canonical-parent shared-edge-cover package on the route-facing exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoCover⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoCover⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for the same-embedding raw canonical-parent shared-edge-cover package. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
  exact
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of the raw canonical-parent shared-edge cover already
refutes a universal derivation of that source-fixed cover burden. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
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
  refine
    (not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hNoCover⟩
    exact
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoCover⟩
  · intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
      hv23
    exact
      h emb boundaryData dartCycles hboundaryArc hcurrent C hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        a b faceBoundary hv23

/-- The same exact one-collar refinement also fails to force the same-embedding annulus-root
parent-peel package on the actual successor-cycle boundary-order shell of the exact-v23
live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier wheel shell sufficient for the same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := wheelWithInnerTriangleGraph)
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
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hCarrier a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle
live-carrier shell together with failure of annulus-root parent-peel data already refutes a
universal derivation of that source-fixed parent-peel burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) :
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoParentPeel⟩
  exact hNoParentPeel (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
    faceBoundary hv23)

/-- The same exact one-collar refinement still does not force the same-embedding annulus-root
parent-peel package on the actual endpoint-bearing successor-cycle boundary-order shell of the
exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoParentPeel⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoParentPeel⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for the same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of annulus-root parent-peel data already refutes a
universal derivation of that source-fixed parent-peel burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) :
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
    (not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hNoParentPeel⟩
    exact
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoParentPeel⟩
  · intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
      hv23
    exact
      h emb boundaryData dartCycles hboundaryArc hcurrent C hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        a b faceBoundary hv23

/-- Exact-v23 annulus-root parent-peel wheel separation at graph-vs-fixed-embedding level: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed route-facing one-collar wheel shell with the same coloring and surviving purified
carrier still fails the same-embedding annulus-root parent-peel package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusRootParentPeelData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨by
        refine
          ⟨allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph, ?_⟩
        letI : Inhabited wheelWithInnerTriangleGraph.edgeSet := ⟨wit01⟩
        exact
          theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
            (G := wheelWithInnerTriangleGraph)
            (degeneratePlanarBoundaryAttachedRootedFacePeelCertificate
              wheelWithInnerTriangleGraph)
            wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Honest-source reformulation of the same exact-v23 annulus-root parent-peel wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed one-collar wheel shell already carries an honest closed-walk source
with the same surviving purified carrier and still fails the same-embedding annulus-root
parent-peel package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_planarBoundaryAnnulusRootParentPeelData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusRootParentPeelData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoParentPeel⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoParentPeel⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing graph-level annulus-root parent-peel wheel separation: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
route-facing exact-v23 one-collar wheel shell already carries a real unblocked endpoint and
still fails the same-embedding annulus-root parent-peel package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusRootParentPeelData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusRootParentPeelData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoParentPeel⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).2 hCarrier,
      a, b, faceBoundary, hv23, hNoParentPeel⟩

/-- Honest-source reformulation of the same endpoint-bearing annulus-root parent-peel wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails the same-embedding
annulus-root parent-peel package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusRootParentPeelData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusRootParentPeelData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoParentPeel⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoParentPeel⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- The same exact one-collar refinement still does not force the downstream positive
construction face-layer package on the actual successor-cycle boundary-order shell of the
exact-v23 live-carrier wheel benchmark. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Joint obstruction on the actual successor-cycle exact-v23 wheel shell: the same fixed
embedding simultaneously exhibits a concrete face boundary carrying two distinct interior edges
and still fails the upstream positive construction face-layer package.  This records the
nondegenerate wheel obstruction at the benchmark geometry itself, rather than only through a
downstream route-facing failed universal. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  (∃ f : AmbientFace emb.faces,
                    ∃ e₁ ∈ emb.faceBoundary f.1,
                      ∃ e₂ ∈ emb.faceBoundary f.1,
                        e₁ ≠ e₂ ∧
                          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                          e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Exact one-collar current-boundary data also fails to make the successor-cycle exact-v23
live-carrier wheel shell sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := wheelWithInnerTriangleGraph)
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
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary))
      ?_ ?_
  · rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness_wheelWithInnerTriangle with
      ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
        faceBoundary, hv23, hforce⟩
    exact
      ⟨emb,
        ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
          faceBoundary, hv23⟩,
        hforce⟩
  · intro emb hP
    rcases hP with
      ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, hCarrier, a, b,
        faceBoundary, hv23⟩
    exact h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC hCarrier a b
      faceBoundary hv23

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle
live-carrier shell together with failure of construction face-layer data already refutes a
universal derivation of that downstream positive face-layer burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) :
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoFaceLayer⟩
  exact hNoFaceLayer (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
    faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not force the downstream positive
construction face-layer package on the actual successor-cycle exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoFaceLayer⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoFaceLayer⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for the downstream positive construction face-layer package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of construction face-layer data already refutes a
universal derivation of that downstream positive face-layer burden. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) :
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
    (not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G) ?_) ?_
  · rcases hWitness with
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
        faceBoundary, hv23, hNoFaceLayer⟩
    exact
      ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
        (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).1 hEndpoint,
        a, b, faceBoundary, hv23, hNoFaceLayer⟩
  · intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
      hv23
    exact
      h emb boundaryData dartCycles hboundaryArc hcurrent C hC
        ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
          emb).2 hnonempty)
        a b faceBoundary hv23

/-- The fixed wheel embedding cannot support any annulus decomposition together with witness
ownership: any such witness assignment would induce annulus collar geometry on the same
embedding, contradicting the existing wheel geometry obstruction. -/
theorem not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle :
    ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition wheelWithInnerTriangleEmbedding,
        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
      ((nonempty_planarBoundaryAnnulusCollarGeometry_iff_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment).2
        h)

/-- Even after adding exact one-collar current-boundary data, the honest closed-walk exact-v23
live-carrier wheel shell still does not force witness ownership on any same-embedding annulus
decomposition. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the honest closed-walk exact-v23
live-carrier wheel shell sufficient for any same-embedding annulus decomposition with witness
ownership. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk
live-carrier shell together with failure of annulus witness ownership already refutes a universal
derivation of that downstream decomposition-and-witness burden. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoWitnessAssignment⟩
  exact hNoWitnessAssignment (h emb source hcurrent C hC hCarrier a b faceBoundary hv23)

/-- Even after adding exact one-collar current-boundary data, the route-facing successor-cycle
exact-v23 wheel shell still does not force witness ownership on any same-embedding annulus
decomposition. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the route-facing successor-cycle
exact-v23 live-carrier wheel shell sufficient for any same-embedding annulus decomposition with
witness ownership. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle
live-carrier shell together with failure of annulus witness ownership already refutes a
universal derivation of that downstream decomposition-and-witness burden. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
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
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoWitnessAssignment⟩
  exact hNoWitnessAssignment (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hCarrier a b
    faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not force annulus witness ownership
on the honest exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoWitnessAssignment⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoWitnessAssignment⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar wheel shell
sufficient for any same-embedding annulus decomposition carrying witness ownership. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source hcurrent C hC hnonempty a b faceBoundary hv23
        exact
          h emb source hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of annulus witness ownership already refutes a universal
derivation of that downstream decomposition-and-witness burden. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    (not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23,
            hNoWitnessAssignment⟩
        exact
          ⟨emb, source, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoWitnessAssignment⟩)
      (by
        intro emb source hcurrent C hC hnonempty a b faceBoundary hv23
        exact
          h emb source hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23))

/-- Adjoining a named unblocked interior endpoint still does not force annulus witness ownership
on the route-facing exact-v23 one-collar wheel shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hCarrier, a, b, faceBoundary,
      hv23, hNoWitnessAssignment⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoWitnessAssignment⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for any same-embedding annulus decomposition carrying witness ownership. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of annulus witness ownership already refutes a
universal derivation of that downstream decomposition-and-witness burden. -/
theorem
    not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
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
                      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
                        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  intro h
  exact
    (not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b,
            faceBoundary, hv23, hNoWitnessAssignment⟩
        exact
          ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoWitnessAssignment⟩)
      (by
        intro emb boundaryData dartCycles hboundaryArc hcurrent C hC hnonempty a b faceBoundary
            hv23
        exact
          h emb boundaryData dartCycles hboundaryArc hcurrent C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23))

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

/-- Graph-level packaging of the same wheel obstruction on the honest source shell: the wheel
graph admits an embedding with honest closed-walk source data, an explicit Tait coloring, and a
local unblocked interior endpoint, while the same embedding still lacks
`InteriorDualBoundaryRootAdjDistancePeelData`. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- The honest closed-walk source shell does not generically force same-embedding IDBRAD.  The
wheel benchmark already has the source, Tait coloring, and local endpoint witness required by
the raw source-IDBRAD bridge, while the target IDBRAD datum still fails there. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph
      with ⟨emb, source, C, hC, hEndpoint, hNoIDBRAD⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoIDBRAD (hTarget C hC hEndpoint)⟩

/-- Graph-level packaging of the same wheel obstruction on the live successor-cycle shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- The live successor-cycle shell also does not generically force same-embedding IDBRAD.  So
the missing source-side bridge is genuinely the cycle-breaking interior-dual/witness-cover
construction itself, not just one more packaging step around already sufficient source fields. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
                HasUnblockedInteriorEndpoint emb →
                  Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            HasUnblockedInteriorEndpoint emb →
              Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph
      with ⟨emb, boundaryData, dartCycles, hArc, C, hC, hEndpoint, hNoIDBRAD⟩
  exact
    ⟨emb, boundaryData, dartCycles, hArc, by
      intro hTarget
      exact hNoIDBRAD (hTarget C hC hEndpoint)⟩

/-- The wheel graph still admits the full theorem-4.9 synthesis endpoint for the explicit Tait
coloring at the graph level: the degenerate all-boundary embedding supplies an attached
certificate, so the current synthesis theorem fires there even though the honest wheel embedding
fails the live source-preserving IDBRAD burden. -/
theorem
    wheelWithInnerTriangleDegenerateEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis
      (allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
      wheelWithInnerTriangleTaitEdgeColoring := by
  letI : Inhabited wheelWithInnerTriangleGraph.edgeSet := ⟨wit01⟩
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := wheelWithInnerTriangleGraph)
      (degeneratePlanarBoundaryAttachedRootedFacePeelCertificate
        wheelWithInnerTriangleGraph)
      wheelWithInnerTriangleTaitEdgeColoring wheelWithInnerTriangleTaitEdgeColoring_isTait

/-- The known graph-level wheel witness already sits off the projected nonempty lane: the
degenerate all-boundary embedding reaches the full theorem-4.9 synthesis endpoint, but its
selected-boundary-purified interior-edge carrier is empty and therefore cannot witness the
projected nonempty endpoint. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_degenerateSynthesis_blocks_nonemptyProjectedSynthesis
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph wheelWithInnerTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis
        (allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        wheelWithInnerTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices
          (allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph) =
        ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis
        (allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        wheelWithInnerTriangleTaitEdgeColoring := by
  refine
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      wheelWithInnerTriangleDegenerateEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
        wheelWithInnerTriangleGraph,
      ?_⟩
  intro hProjected
  have hCarrier := hProjected.nonemptySynthesis.carrier_nonempty
  rw [selectedBoundaryInteriorEdgeEndpointVertices_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
      wheelWithInnerTriangleGraph] at hCarrier
  simp at hCarrier

/-- The wheel graph still admits the full theorem-4.9 synthesis endpoint for the explicit Tait
coloring at the graph level: the degenerate all-boundary embedding supplies an attached
certificate, so the current synthesis theorem fires there even though the honest wheel embedding
fails the live source-preserving IDBRAD burden. -/
theorem
    exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring := by
  exact
    ⟨allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      wheelWithInnerTriangleDegenerateEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring⟩

/-- The current graph-level positive wheel witness necessarily changes embeddings: the degenerate
all-boundary witness has empty selected-boundary-purified interior-edge carrier, while the honest
source-preserving wheel embedding has a surviving purified carrier. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_requires_embedding_change
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring ∧
        emb ≠ wheelWithInnerTriangleEmbedding ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty := by
  refine
    ⟨allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      wheelWithInnerTriangleDegenerateEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      ?_, selectedBoundaryInteriorEdgeEndpointVertices_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
        wheelWithInnerTriangleGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩
  intro hEq
  have hCarrier :
      (selectedBoundaryInteriorEdgeEndpointVertices
        (allEdgesBoundaryPlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)).Nonempty := by
    simpa [hEq] using selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rw [selectedBoundaryInteriorEdgeEndpointVertices_allEdgesBoundaryPlaneEmbeddingWithBoundary_eq_empty
      wheelWithInnerTriangleGraph] at hCarrier
  simp at hCarrier

/-- The wheel graph cleanly separates graph-level Theorem~4.9 synthesis from the live same-
embedding route burden.  The graph admits synthesis for the explicit Tait coloring on some
embedding, but the honest closed-walk wheel embedding with the same coloring and an explicit
unblocked interior endpoint still cannot supply generic IDBRAD. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_IDBRAD_obstruction
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Stronger wheel separation theorem: the graph still admits the full theorem-4.9 synthesis
endpoint for the explicit Tait coloring on some embedding, while the honest source-preserving
wheel embedding with the same coloring fails every currently sufficient same-embedding
selector/acyclic endpoint used in the live route and also fails generic IDBRAD. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_selector_or_acyclicEndpoint_or_IDBRAD
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
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
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Projected-endpoint strengthening of the wheel separation theorem: the graph still admits full
theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the honest
source-preserving wheel embedding with the same coloring fails both currently formalized
same-embedding source-to-projected-endpoint routes. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_sameEmbedding_projectedSourceRoutes
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      (Nonempty
          (PlanarBoundaryClosedWalkAnnulusBoundarySource
            wheelWithInnerTriangleEmbedding) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource
              wheelWithInnerTriangleEmbedding,
            ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData
              wheelWithInnerTriangleEmbedding.faces
                wheelWithInnerTriangleEmbedding.faceBoundary,
              Theorem49BoundaryRootNonemptyProjectedSynthesis
                wheelWithInnerTriangleEmbedding
                wheelWithInnerTriangleTaitEdgeColoring) ∧
      (Nonempty
          (PlanarBoundaryClosedWalkAnnulusBoundarySource
            wheelWithInnerTriangleEmbedding) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ¬ ∃ source :
              PlanarBoundaryClosedWalkAnnulusBoundarySource
                wheelWithInnerTriangleEmbedding,
            ∃ peelFaces :
              Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
            ∃ hunique : PairwiseUniqueSharedInteriorEdges
              wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces,
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
                  (selectedBoundarySupport
                    wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces
                    wheelWithInnerTriangleEmbedding.faces)) ∧
              interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
                (rootedSharedInteriorEdgeOfPairwiseUnique
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces hunique
                  (interiorDualSpanningForestRoot
                    wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots)
                  source.fallbackEdge) ∧
              (∀ f ∈ peelFaces, ∀ e ∈
                  (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces hunique
                      (interiorDualSpanningForestRoot
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                e ∈ selectedBoundarySupport
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces
                      wheelWithInnerTriangleEmbedding.faces ∨
                  ∃ g ∈ peelFaces,
                    parentTowardsRoot
                        (interiorDualSpanningForest
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (interiorDualSpanningForestRoot
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                    e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) ∧
              Theorem49BoundaryRootNonemptyProjectedSynthesis
                wheelWithInnerTriangleEmbedding
                wheelWithInnerTriangleTaitEdgeColoring) := by
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_based_projectedSynthesis,
      wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_boundaryFaceRootsCanonicalParent_based_projectedSynthesis⟩

/-- Nondegenerate projected-route strengthening of the wheel separation theorem: the graph still
admits full theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
honest source-preserving wheel embedding keeps a concrete two-interior-edge face boundary and
still fails both currently formalized same-embedding source-to-projected-endpoint routes. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_sameEmbedding_projectedSourceRoutes
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
        ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
          ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport
                wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces ∧
              e₂ ∈ interiorEdgeSupport
                wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces) ∧
      (Nonempty
          (PlanarBoundaryClosedWalkAnnulusBoundarySource
            wheelWithInnerTriangleEmbedding) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource
              wheelWithInnerTriangleEmbedding,
            ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData
              wheelWithInnerTriangleEmbedding.faces
                wheelWithInnerTriangleEmbedding.faceBoundary,
              Theorem49BoundaryRootNonemptyProjectedSynthesis
                wheelWithInnerTriangleEmbedding
                wheelWithInnerTriangleTaitEdgeColoring) ∧
      (Nonempty
          (PlanarBoundaryClosedWalkAnnulusBoundarySource
            wheelWithInnerTriangleEmbedding) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ¬ ∃ source :
              PlanarBoundaryClosedWalkAnnulusBoundarySource
                wheelWithInnerTriangleEmbedding,
            ∃ peelFaces :
              Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
            ∃ hunique : PairwiseUniqueSharedInteriorEdges
              wheelWithInnerTriangleEmbedding.faceBoundary
                wheelWithInnerTriangleEmbedding.faces,
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
                  (selectedBoundarySupport
                    wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces
                    wheelWithInnerTriangleEmbedding.faces)) ∧
              interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces ⊆ peelFaces.image
                (rootedSharedInteriorEdgeOfPairwiseUnique
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces hunique
                  (interiorDualSpanningForestRoot
                    wheelWithInnerTriangleEmbedding.faceBoundary
                    wheelWithInnerTriangleEmbedding.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots)
                  source.fallbackEdge) ∧
              (∀ f ∈ peelFaces, ∀ e ∈
                  (wheelWithInnerTriangleEmbedding.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces hunique
                      (interiorDualSpanningForestRoot
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                e ∈ selectedBoundarySupport
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces
                      wheelWithInnerTriangleEmbedding.faces ∨
                  ∃ g ∈ peelFaces,
                    parentTowardsRoot
                        (interiorDualSpanningForest
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)
                        (interiorDualSpanningForestRoot
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                    e ∈ wheelWithInnerTriangleEmbedding.faceBoundary g.1) ∧
              Theorem49BoundaryRootNonemptyProjectedSynthesis
                wheelWithInnerTriangleEmbedding
                wheelWithInnerTriangleTaitEdgeColoring) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_sameEmbedding_projectedSourceRoutes with
    ⟨hsynth, hCarrier, hNoIDBRADRoute, hNoParentRoute⟩
  exact
    ⟨hsynth, hCarrier, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoIDBRADRoute, hNoParentRoute⟩

/-- Replacement-positive strengthening of the wheel separation theorem: the graph still admits
full theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the honest
source-preserving wheel embedding with the same coloring and surviving purified carrier still
fails both currently formalized direct replacement-positive packages and the repaired
previous-boundary witness geometry. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_naturalResidualSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same natural-residual wheel separation: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
exact-v23 one-collar wheel shell already carries an honest closed-walk source with the same
surviving purified carrier and still fails every current natural residual same-embedding witness
package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_naturalResidualSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (ResidualBoundarySelectorData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_naturalResidualSameEmbeddingGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoResidual, hNoSelector, hNoHeight, hNoCollar⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoResidual, hNoSelector, hNoHeight, hNoCollar⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Honest-source reformulation of the same nondegenerate natural-residual wheel separation: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with the
same surviving purified carrier, a concrete two-interior-edge face boundary, and still fails
every current natural residual same-embedding witness package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_naturalResidualSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Nonempty
                  (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (ResidualBoundarySelectorData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_naturalResidualSameEmbeddingGeometry with
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23, hNoResidual,
      hNoSelector, hNoHeight, hNoCollar⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoResidual,
      hNoSelector, hNoHeight, hNoCollar⟩

/-- Joint exact-shell wheel obstruction: even after adjoining graph-level theorem-4.9 synthesis
for the explicit Tait coloring, the fixed exact-v23 successor-cycle one-collar wheel shell still
carries a concrete face boundary with two distinct interior edges while lacking every current
natural residual same-embedding witness package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_naturalResidualSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle⟩

/-- Replacement-positive strengthening of the wheel separation theorem: the graph still admits
full theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the honest
source-preserving wheel embedding with the same coloring and surviving purified carrier still
fails both currently formalized direct replacement-positive packages and the repaired
previous-boundary witness geometry. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_replacementPositiveProjectedGeometry_or_previousBoundaryWitness
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_wheelWithInnerTriangle⟩

/-- Exact-v23 successor-cycle replacement-positive strengthening of the wheel separation theorem:
the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding,
while the fixed successor-cycle exact-v23 one-collar wheel shell with the same coloring and
surviving purified carrier still fails every current direct or route-facing replacement-positive
package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same exact-v23 replacement-positive wheel separation: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with the
same surviving purified carrier and still fails every current direct or route-facing
replacement-positive package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_replacementPositiveProjectedGeometryOn with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Honest-source reformulation of the same nondegenerate replacement-positive wheel separation:
the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding,
while the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source
with the same surviving purified carrier, a concrete two-interior-edge face boundary, and still
fails every current direct or route-facing replacement-positive package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_replacementPositiveProjectedGeometryOn with
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23, hNoHeight,
      hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoHeight,
      hNoCollar, hNoClosedWalk, hNoSuccessor⟩

/-- Joint exact-shell replacement-positive wheel obstruction: even after adjoining graph-level
theorem-4.9 synthesis for the explicit Tait coloring, the fixed exact-v23 successor-cycle
one-collar wheel shell still carries a concrete face boundary with two distinct interior edges
while lacking every current direct or route-facing replacement-positive package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_replacementPositiveProjectedGeometryOn with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩

/-- Endpoint-bearing replacement-positive strengthening of the wheel separation theorem: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed successor-cycle exact-v23 one-collar wheel shell with a real unblocked endpoint still fails
every current direct or route-facing replacement-positive package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding ∧
                ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                  wheelWithInnerTriangleEmbedding := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same endpoint-bearing replacement-positive wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails every current direct or
route-facing replacement-positive package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding ∧
              ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                wheelWithInnerTriangleEmbedding := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hTwoEdges, hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23, hTwoEdges,
      hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing current-sufficient strengthening of the wheel separation theorem: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed successor-cycle exact-v23 one-collar wheel shell with a real unblocked endpoint still
fails every currently sufficient same-embedding geometry endpoint. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (BoundaryRootedFacePeelCertificate
                      wheelWithInnerTriangleEmbedding.faces.attach
                      (ambientFaceBoundary
                        (allFaces := wheelWithInnerTriangleEmbedding.faces)
                        wheelWithInnerTriangleEmbedding.faceBoundary)) ∧
                ¬ Nonempty
                    (PlanarBoundaryWellFoundedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusCollarGeometry
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same endpoint-bearing current-sufficient wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails every currently sufficient
same-embedding geometry endpoint. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (BoundaryRootedFacePeelCertificate
                    wheelWithInnerTriangleEmbedding.faces.attach
                    (ambientFaceBoundary
                      (allFaces := wheelWithInnerTriangleEmbedding.faces)
                      wheelWithInnerTriangleEmbedding.faceBoundary)) ∧
              ¬ Nonempty
                  (PlanarBoundaryWellFoundedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusCollarGeometry
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoHeight, hNoCollar, hNoCert, hNoWellFounded, hNoAnnulus⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoHeight, hNoCollar, hNoCert, hNoWellFounded, hNoAnnulus⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Face-layer strengthening of the wheel separation theorem: the graph still admits the full
theorem-4.9 endpoint for the explicit Tait coloring on some embedding, while the honest
successor-cycle exact-v23 one-collar wheel shell with the same coloring and surviving purified
carrier still does not force the positive construction face-layer package on that same embedding. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Honest-source reformulation of the same construction-face-layer wheel separation: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with the
same surviving purified carrier and still fails the same-embedding construction face-layer
package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoConstruction⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoConstruction⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Honest-source reformulation of the same nondegenerate construction-face-layer wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with the same surviving purified carrier, a concrete two-interior-edge face
boundary, and still fails the same-embedding construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoConstruction⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoConstruction⟩

/-- Joint exact-shell construction-face-layer wheel obstruction: even after adjoining graph-level
theorem-4.9 synthesis for the explicit Tait coloring, the fixed exact-v23 successor-cycle
one-collar wheel shell still carries a concrete face boundary with two distinct interior edges
while lacking the same-embedding construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoConstruction⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoConstruction⟩

/-- Endpoint-bearing construction-face-layer strengthening of the wheel separation theorem: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed route-facing exact-v23 one-collar wheel shell with a real unblocked endpoint still
fails the same-embedding construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩

/-- Honest-source reformulation of the same endpoint-bearing construction-face-layer wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails the same-embedding
construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoConstruction⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoConstruction⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing nondegenerate construction-face-layer strengthening of the wheel separation
theorem: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed route-facing exact-v23 one-collar wheel shell with a real unblocked
endpoint still carries a concrete two-interior-edge face boundary and fails the same-embedding
construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoConstruction⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoConstruction⟩

/-- Honest-source reformulation of the same endpoint-bearing nondegenerate construction-face-layer
wheel separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on
some embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint, a concrete two-interior-edge face boundary,
and still fails the same-embedding construction face-layer package. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hTwoEdges, hNoConstruction⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hTwoEdges, hNoConstruction⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Strongest current wheel separation theorem: the graph still admits the full theorem-4.9
endpoint for the explicit Tait coloring on some embedding, while the honest successor-cycle
exact-v23 one-collar wheel shell with the same coloring and surviving purified carrier still
does not force any same-embedding annulus decomposition carrying witness ownership. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ ∃ decomp :
                    PlanarBoundaryAnnulusDecomposition
                      wheelWithInnerTriangleEmbedding,
                    Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle⟩

/-- Honest-source reformulation of the same annulus-witness-assignment wheel separation: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with the
same surviving purified carrier and still fails witness ownership on every same-embedding annulus
decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∃ decomp :
                  PlanarBoundaryAnnulusDecomposition
                    wheelWithInnerTriangleEmbedding,
                  Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoWitness⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hCarrier, a, b, faceBoundary, hv23,
      hNoWitness⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing graph-level annulus-witness-assignment wheel separation: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
route-facing exact-v23 one-collar wheel shell already carries a real unblocked endpoint and
still fails witness ownership on every same-embedding annulus decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ ∃ decomp :
                    PlanarBoundaryAnnulusDecomposition
                      wheelWithInnerTriangleEmbedding,
                    Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoWitness⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).2 hCarrier,
      a, b, faceBoundary, hv23, hNoWitness⟩

/-- Honest-source reformulation of the same endpoint-bearing annulus-witness-assignment wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails witness ownership on every
same-embedding annulus decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∃ decomp :
                  PlanarBoundaryAnnulusDecomposition
                    wheelWithInnerTriangleEmbedding,
                  Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoWitness⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoWitness⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Nondegenerate annulus-witness-assignment strengthening of the wheel separation theorem: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed successor-cycle exact-v23 one-collar wheel shell still carries a concrete
two-interior-edge face boundary and fails witness ownership on every same-embedding annulus
decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ ∃ decomp :
                    PlanarBoundaryAnnulusDecomposition
                      wheelWithInnerTriangleEmbedding,
                    Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, hNoWitness⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hCarrier, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoWitness⟩

/-- Honest-source reformulation of the same nondegenerate annulus-witness-assignment wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with the same surviving purified carrier, a concrete two-interior-edge face
boundary, and still fails witness ownership on every same-embedding annulus decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ ∃ decomp :
                  PlanarBoundaryAnnulusDecomposition
                    wheelWithInnerTriangleEmbedding,
                  Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23, hNoWitness⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hCarrier, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoWitness⟩

/-- Endpoint-bearing nondegenerate annulus-witness-assignment strengthening of the wheel
separation theorem: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring
on some embedding, while the fixed route-facing exact-v23 one-collar wheel shell with a real
unblocked endpoint still carries a concrete two-interior-edge face boundary and fails witness
ownership on every same-embedding annulus decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ ∃ decomp :
                    PlanarBoundaryAnnulusDecomposition
                      wheelWithInnerTriangleEmbedding,
                    Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoWitness⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoWitness⟩

/-- Honest-source reformulation of the same endpoint-bearing nondegenerate
annulus-witness-assignment wheel separation: the graph still admits theorem-4.9 synthesis for
the explicit Tait coloring on some embedding, while the fixed exact-v23 one-collar wheel shell
already carries an honest closed-walk source with a real unblocked endpoint, a concrete
two-interior-edge face boundary, and still fails witness ownership on every same-embedding
annulus decomposition. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ ∃ decomp :
                  PlanarBoundaryAnnulusDecomposition
                    wheelWithInnerTriangleEmbedding,
                  Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment with
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23, hNoWitness⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoWitness⟩

/-- Exact one-collar current-boundary data does not make the honest closed-walk exact-v23 wheel
shell satisfy the facewise at-most-one local premise.  The fixed wheel embedding still has a
face carrying two distinct interior boundary edges. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- The honest closed-walk exact-v23 one-collar shell does not generically force the facewise
at-most-one interior-edge premise.  The wheel benchmark already provides the counterexample. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  intro h
  exact
    not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk shell
together with failure of the facewise at-most-one interior-edge premise already refutes a
universal derivation of that downstream local-cardinality burden. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, a, b, faceBoundary, hv23, hNotAtMostOne⟩
  exact hNotAtMostOne (h emb source hcurrent C hC a b faceBoundary hv23)

/-- The same exact-v23 one-collar failure persists on the route-facing successor-cycle shell:
the wheel benchmark still does not satisfy the facewise at-most-one local premise on that same
embedding. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- The route-facing successor-cycle exact-v23 one-collar shell also does not generically force
the facewise at-most-one interior-edge premise. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with failure of the facewise at-most-one interior-edge premise already refutes a
universal derivation of that downstream local-cardinality burden. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
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
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, a, b, faceBoundary, hv23,
      hNotAtMostOne⟩
  exact hNotAtMostOne (h emb boundaryData dartCycles hboundaryArc hcurrent C hC a b faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not make the honest exact-v23
one-collar wheel shell satisfy the facewise at-most-one local premise. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- The named unblocked endpoint still does not make the honest exact-v23 one-collar shell
generically force the facewise at-most-one interior-edge premise. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ (C : wheelWithInnerTriangleGraph.EdgeColoring Color),
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  intro h
  exact
    not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
        (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
          wheelWithInnerTriangleClosedWalkAnnulusBoundarySource)
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with failure of the facewise at-most-one interior-edge premise already
refutes a universal derivation of that downstream local-cardinality burden. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hNotAtMostOne⟩
  exact hNotAtMostOne (h emb source hcurrent C hC hEndpoint a b faceBoundary hv23)

/-- Adjoining a named unblocked interior endpoint still does not make the route-facing exact-v23
one-collar wheel shell satisfy the facewise at-most-one local premise. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar shell
generically force the facewise at-most-one interior-edge premise. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  intro h
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace
      (h wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        hcurrent
        wheelWithInnerTriangleTaitEdgeColoring
        wheelWithInnerTriangleTaitEdgeColoring_isTait
        hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
        red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
        nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with failure of the facewise at-most-one interior-edge premise
already refutes a universal derivation of that downstream local-cardinality burden. -/
theorem
    not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
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
                      ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, hcurrent, C, hC, hEndpoint, a, b, faceBoundary,
      hv23, hNotAtMostOne⟩
  exact hNotAtMostOne (h emb boundaryData dartCycles hboundaryArc hcurrent C hC hEndpoint a b faceBoundary hv23)

/-- Exact-shell local-cardinality strengthening of the wheel separation theorem: the graph still
admits the theorem-4.9 endpoint for the explicit Tait coloring on some embedding, while the
fixed route-facing exact-v23 one-collar shell on the wheel benchmark still fails the facewise
at-most-one local premise needed by the direct exact-shell closure theorem. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- Honest-source reformulation of the same local-cardinality wheel separation: the graph still
admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the fixed
exact-v23 one-collar wheel shell already carries an honest closed-walk source and still fails
the facewise at-most-one local premise needed by the direct exact-shell closure theorem. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, a, b, faceBoundary, hv23,
      hNoAtMostOne⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, a, b, faceBoundary, hv23, hNoAtMostOne⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Endpoint-bearing local-cardinality strengthening of the wheel separation theorem: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed route-facing exact-v23 one-collar wheel shell with a real unblocked endpoint still fails
the facewise at-most-one local premise needed by the direct exact-shell closure theorem. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      hasUnblockedInteriorEndpoint_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩

/-- Honest-source reformulation of the same endpoint-bearing local-cardinality wheel
separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint and still fails the facewise at-most-one
local premise needed by the direct exact-shell closure theorem. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoAtMostOne⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ⟨data, hnum, ?_⟩, hTait, hEndpoint, a, b, faceBoundary, hv23,
      hNoAtMostOne⟩
  simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
    PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
    hboundary

/-- Nondegenerate local-cardinality strengthening of the wheel separation theorem: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed successor-cycle exact-v23 one-collar wheel shell still carries a concrete two-interior-
edge face boundary and fails the facewise at-most-one interior-edge premise. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, a, b, faceBoundary, hv23,
      hNoAtMostOne⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoAtMostOne⟩

/-- Honest-source reformulation of the same nondegenerate local-cardinality wheel separation:
the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding,
while the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source, a
concrete two-interior-edge face boundary, and still fails the facewise at-most-one interior-edge
premise. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, source, hcurrent, hTait, a, b, faceBoundary, hv23, hNoAtMostOne⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoAtMostOne⟩

/-- Endpoint-bearing nondegenerate local-cardinality strengthening of the wheel separation
theorem: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed route-facing exact-v23 one-collar wheel shell with a real unblocked
endpoint still carries a concrete two-interior-edge face boundary and fails the facewise
at-most-one interior-edge premise. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data :
              PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, hNoAtMostOne⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, hcurrent, hTait, hEndpoint, a, b,
      faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoAtMostOne⟩

/-- Honest-source reformulation of the same endpoint-bearing nondegenerate local-cardinality
wheel separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on
some embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint, a concrete two-interior-edge face boundary,
and still fails the facewise at-most-one interior-edge premise. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace with
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23, hNoAtMostOne⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoAtMostOne⟩

/-- Consolidated exact-v23 no-endpoint wheel obstruction: the route-facing successor-cycle
one-collar shell with real Tait coloring and surviving purified carrier simultaneously fails the
current selector, canonical-parent, parent-peel, face-layer, residual, acyclic, collar, and
facewise-at-most-one repairs on the same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  refine
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle,
      ?_,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      (G := wheelWithInnerTriangleGraph)
      ⟨wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
        peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the honest-source exact-v23
one-collar shell sufficient for any currently known no-endpoint same-embedding repair on the
wheel benchmark. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) := by
  intro h
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  rcases h emb source C a b faceBoundary hcurrent hC hCarrier hv23 with
    hSelector | hRaw | hParent | hConstruction | hResidual | hResidualSelector | hHeight |
      hCollar | hWellFounded | hAnnulus | hAtMostOne
  · exact hNoSelector hSelector
  · exact hNoRaw hRaw
  · exact hNoParent hParent
  · exact hNoConstruction hConstruction
  · exact hNoResidual hResidual
  · exact hNoResidualSelector hResidualSelector
  · exact hNoHeight hHeight
  · exact hNoCollar hCollar
  · exact hNoWellFounded hWellFounded
  · exact hNoAnnulus hAnnulus
  · exact hNoAtMostOne hAtMostOne

/-- Any explicit same-embedding witness of the exact one-collar/v23 honest closed-walk shell
together with simultaneous failure of every currently known no-endpoint same-embedding repair
already refutes a universal derivation of that bundled no-endpoint burden. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) := by
  intro h
  rcases hWitness with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  rcases h emb source C a b faceBoundary hcurrent hC hCarrier hv23 with
    hSelector | hRaw | hParent | hConstruction | hResidual | hResidualSelector | hHeight |
      hCollar | hWellFounded | hAnnulus | hAtMostOne
  · exact hNoSelector hSelector
  · exact hNoRaw hRaw
  · exact hNoParent hParent
  · exact hNoConstruction hConstruction
  · exact hNoResidual hResidual
  · exact hNoResidualSelector hResidualSelector
  · exact hNoHeight hHeight
  · exact hNoCollar hCollar
  · exact hNoWellFounded hWellFounded
  · exact hNoAnnulus hAnnulus
  · exact hNoAtMostOne hAtMostOne

/-- Consolidated exact-v23 no-endpoint wheel obstruction: the route-facing successor-cycle
one-collar shell with real Tait coloring and surviving purified carrier simultaneously fails the
current selector, canonical-parent, parent-peel, face-layer, residual, acyclic, collar, and
facewise-at-most-one repairs on the same embedding. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                    ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                    ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                    ¬ ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  refine
    ⟨wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle,
      ?_,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      (G := wheelWithInnerTriangleGraph)
      ⟨wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
        wheelWithInnerTriangleDartSuccessorCycleGeometry,
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
        peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- Exact one-collar current-boundary data also fails to make the route-facing exact-v23
successor-cycle shell sufficient for any currently known no-endpoint same-embedding repair on
the wheel benchmark. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 →
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                      (∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) := by
  intro h
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC, hCarrier, a, b,
      faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  rcases h emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC hCarrier a b
      faceBoundary hv23 with
    hSelector | hRaw | hParent | hConstruction | hResidual | hResidualSelector | hHeight |
      hCollar | hWellFounded | hAnnulus | hAtMostOne
  · exact hNoSelector hSelector
  · exact hNoRaw hRaw
  · exact hNoParent hParent
  · exact hNoConstruction hConstruction
  · exact hNoResidual hResidual
  · exact hNoResidualSelector hResidualSelector
  · exact hNoHeight hHeight
  · exact hNoCollar hCollar
  · exact hNoWellFounded hWellFounded
  · exact hNoAnnulus hAnnulus
  · exact hNoAtMostOne hAtMostOne

/-- Any explicit same-embedding witness of the exact one-collar/v23 successor-cycle shell
together with simultaneous failure of every currently known no-endpoint same-embedding repair
already refutes a universal derivation of that bundled no-endpoint burden. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
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
                    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                    ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                    ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                    ¬ ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 →
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
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
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                      (∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC, hCarrier, a, b,
      faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  rcases h emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC hCarrier a b
      faceBoundary hv23 with
    hSelector | hRaw | hParent | hConstruction | hResidual | hResidualSelector | hHeight |
      hCollar | hWellFounded | hAnnulus | hAtMostOne
  · exact hNoSelector hSelector
  · exact hNoRaw hRaw
  · exact hNoParent hParent
  · exact hNoConstruction hConstruction
  · exact hNoResidual hResidual
  · exact hNoResidualSelector hResidualSelector
  · exact hNoHeight hHeight
  · exact hNoCollar hCollar
  · exact hNoWellFounded hWellFounded
  · exact hNoAnnulus hAnnulus
  · exact hNoAtMostOne hAtMostOne

/-- Even after upgrading the live honest exact-v23 one-collar no-endpoint wheel shell to a
genuine unblocked interior endpoint, the same embedding still fails every currently bundled
no-endpoint repair package. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
            HasUnblockedInteriorEndpoint emb ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ) := by
  rcases
      exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle with
    ⟨emb, source, hcurrent, C, hC, hCarrier, a, b, faceBoundary, hv23, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨emb, source, hcurrent, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- The named unblocked endpoint still does not make the honest-source exact-v23 one-collar
wheel shell sufficient for any bundled no-endpoint same-embedding repair. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
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
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) := by
  intro h
  exact
    not_forall_some_currentNoEndpointRepairGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23 honest
closed-walk shell together with simultaneous failure of every currently known no-endpoint
same-embedding repair already refutes a universal derivation of that bundled burden. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
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
                  ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                  ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                  ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                  ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                  ¬ ∀ f : AmbientFace emb.faces,
                      ((emb.faceBoundary f.1).filter
                          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                        (1 : ℕ)) :
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
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                Nonempty (ResidualBoundarySelectorData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) := by
  intro h
  exact
    (not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, source, hcurrent, C, hC, hEndpoint, a, b, faceBoundary, hv23, hNoSelector,
            hNoRaw, hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight,
            hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
        exact
          ⟨emb, source, hcurrent, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction,
            hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded,
            hNoAnnulus, hNoAtMostOne⟩)
      (by
        intro emb source C a b faceBoundary hcurrent hC hnonempty hv23
        exact
          h emb source C a b faceBoundary hcurrent hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            hv23))

/-- Even after upgrading the live route-facing exact-v23 one-collar no-endpoint wheel shell to a
genuine unblocked interior endpoint, the same embedding still fails every currently bundled
no-endpoint repair package. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle
    :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C ∧
              HasUnblockedInteriorEndpoint emb ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                    ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                    ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                    ¬ ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ) := by
  rcases
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC, hCarrier, a, b,
      faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- The named unblocked endpoint still does not make the route-facing exact-v23 one-collar wheel
shell sufficient for any bundled no-endpoint same-embedding repair. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle
    :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 →
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData →
          ∀ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C →
              HasUnblockedInteriorEndpoint emb →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
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
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                      (∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) := by
  intro h
  exact
    not_forall_some_currentNoEndpointRepairGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle
      (by
        intro emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC hnonempty a b
            faceBoundary hv23
        exact
          h emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23)

/-- Any explicit same-embedding witness of the endpoint-bearing exact one-collar/v23
successor-cycle shell together with simultaneous failure of every currently known no-endpoint
same-embedding repair already refutes a universal derivation of that bundled burden. -/
theorem
    not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
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
                    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
                    ¬ Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (ResidualBoundarySelectorData emb) ∧
                    ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
                    ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
                    ¬ ∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          ∀ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 →
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData →
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
                      Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
                      Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∨
                      Nonempty (ResidualBoundarySelectorData emb) ∨
                      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                      Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∨
                      (∀ f : AmbientFace emb.faces,
                        ((emb.faceBoundary f.1).filter
                            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                          (1 : ℕ)) := by
  intro h
  exact
    (not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState
      (V := V) (G := G)
      (by
        rcases hWitness with
          ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC,
            hEndpoint, a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent,
            hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
            hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
        exact
          ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, C, hC,
            (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).1 hEndpoint,
            a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction,
            hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded,
            hNoAnnulus, hNoAtMostOne⟩)
      (by
        intro emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC hnonempty a b
            faceBoundary hv23
        exact
          h emb boundaryData dartCycles hboundaryArc data hnum hboundary C hC
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty)
            a b faceBoundary hv23))

/-- Consolidated graph-level separation theorem for the exact-v23 no-endpoint wheel branch: the
explicit Tait coloring still reaches theorem-4.9 synthesis on some embedding, while the fixed
route-facing exact-v23 one-collar wheel shell simultaneously fails every currently known
no-endpoint same-embedding repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
        ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
                (¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                    ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                    ∃ hcoverRoots : RootSetCovers
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                    ∃ hsepRoots : RootSetSeparated
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      (∀ f ∈ peelFaces,
                        Disjoint
                          (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                          (selectedBoundarySupport
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            wheelWithInnerTriangleEmbedding.faces)) ∧
                      interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ⊆
                        peelFaces.image
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces hunique
                            (interiorDualSpanningForestRoot
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryWellFoundedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusCollarGeometry
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            wheelWithInnerTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  rcases hcurrent with ⟨data, hnum, hboundary⟩
  refine
    ⟨exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate,
      wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
      wheelWithInnerTriangleDartSuccessorCycleGeometry,
      wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      data,
      hnum,
      hboundary,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      red, blue,
      (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1),
      nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary,
      not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle,
      ?_,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_residualBoundarySelectorData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace⟩
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      (G := wheelWithInnerTriangleGraph)
      ⟨wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData,
        wheelWithInnerTriangleDartSuccessorCycleGeometry,
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
        peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- Endpoint-bearing graph-level separation theorem for the exact-v23 wheel branch: the explicit
Tait coloring still reaches theorem-4.9 synthesis on some embedding, while the fixed
route-facing exact-v23 one-collar wheel shell already carries a real unblocked endpoint and still
fails every currently bundled no-endpoint same-embedding repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
        ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
                (¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                    ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                    ∃ hcoverRoots : RootSetCovers
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                    ∃ hsepRoots : RootSetSeparated
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      (∀ f ∈ peelFaces,
                        Disjoint
                          (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                          (selectedBoundarySupport
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            wheelWithInnerTriangleEmbedding.faces)) ∧
                      interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ⊆
                        peelFaces.image
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces hunique
                            (interiorDualSpanningForestRoot
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryWellFoundedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusCollarGeometry
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hCarrier,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).2 hCarrier,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- Honest-source reformulation of the same endpoint-bearing graph-level wheel separation: the
graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while
the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source with a
real unblocked endpoint and still fails every currently bundled no-endpoint repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              ¬ Nonempty
                  (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
              (¬ ∃ peelFaces :
                    Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                  ∃ hunique :
                    PairwiseUniqueSharedInteriorEdges
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint
                        (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                        (selectedBoundarySupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          wheelWithInnerTriangleEmbedding.faces)) ∧
                    interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ⊆
                      peelFaces.image
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces hunique
                          (interiorDualSpanningForestRoot
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge)) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (ResidualBoundarySelectorData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryWellFoundedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusCollarGeometry
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hEndpoint,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  refine
    ⟨hsynth, source, ?_, hTait, hEndpoint, a, b, faceBoundary, hv23, hNoSelector, ?_,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  · exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  · simpa [source] using hNoRaw

/-- Nondegenerate strengthening of the bundled no-endpoint wheel separation theorem: the graph
still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding, while the
fixed successor-cycle exact-v23 one-collar wheel shell still carries a concrete two-interior-edge
face boundary and simultaneously fails every currently bundled same-embedding no-endpoint repair.
-/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
        ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          (selectedBoundaryInteriorEdgeEndpointVertices
            wheelWithInnerTriangleEmbedding).Nonempty ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
                (¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                    ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                    ∃ hcoverRoots : RootSetCovers
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                    ∃ hsepRoots : RootSetSeparated
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      (∀ f ∈ peelFaces,
                        Disjoint
                          (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                          (selectedBoundarySupport
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            wheelWithInnerTriangleEmbedding.faces)) ∧
                      interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ⊆
                        peelFaces.image
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces hunique
                            (interiorDualSpanningForestRoot
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryWellFoundedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusCollarGeometry
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hCarrier,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hCarrier,
      a, b, faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector,
      hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- Honest-source reformulation of the same nondegenerate bundled no-endpoint wheel separation:
the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some embedding,
while the fixed exact-v23 one-collar wheel shell already carries an honest closed-walk source, a
concrete two-interior-edge face boundary, and still fails every currently bundled no-endpoint
repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices
          wheelWithInnerTriangleEmbedding).Nonempty ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Nonempty
                  (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
              (¬ ∃ peelFaces :
                    Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                  ∃ hunique :
                    PairwiseUniqueSharedInteriorEdges
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint
                        (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                        (selectedBoundarySupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          wheelWithInnerTriangleEmbedding.faces)) ∧
                    interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ⊆
                      peelFaces.image
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces hunique
                          (interiorDualSpanningForestRoot
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge)) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (ResidualBoundarySelectorData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryWellFoundedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusCollarGeometry
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨hsynth, source, hcurrent, hTait,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        wheelWithInnerTriangleEmbedding).1 hEndpoint,
      a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- Endpoint-bearing nondegenerate strengthening of the bundled no-endpoint wheel separation
theorem: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on some
embedding, while the fixed route-facing exact-v23 one-collar wheel shell with a real unblocked
endpoint still carries a concrete two-interior-edge face boundary and simultaneously fails every
currently bundled same-embedding no-endpoint repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData
              wheelWithInnerTriangleEmbedding,
        ∃ hboundaryArc : ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          IsTaitEdgeColoring wheelWithInnerTriangleGraph
            wheelWithInnerTriangleTaitEdgeColoring ∧
          HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
              Nonempty
                  (V23ResidualBoundaryInitialState
                    wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
                (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                      e₁ ≠ e₂ ∧
                        e₁ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ∧
                        e₂ ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces) ∧
                ¬ Nonempty
                    (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
                (¬ ∃ peelFaces :
                      Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                    ∃ hunique :
                      PairwiseUniqueSharedInteriorEdges
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces,
                    ∃ hcoverRoots : RootSetCovers
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                    ∃ hsepRoots : RootSetSeparated
                      (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                      (∀ f ∈ peelFaces,
                        Disjoint
                          (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                          (selectedBoundarySupport
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            wheelWithInnerTriangleEmbedding.faces)) ∧
                      interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces ⊆
                        peelFaces.image
                          (rootedSharedInteriorEdgeOfPairwiseUnique
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces hunique
                            (interiorDualSpanningForestRoot
                              wheelWithInnerTriangleEmbedding.faceBoundary
                              wheelWithInnerTriangleEmbedding.faces
                              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                              hcoverRoots hsepRoots)
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).fallbackEdge)) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusRootParentPeelData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusConstructionFaceLayerData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (ResidualBoundarySelectorData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryHeightOrderedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryCollarLayerFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryWellFoundedFacePeelWitnessData
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ Nonempty
                    (PlanarBoundaryAnnulusCollarGeometry
                      wheelWithInnerTriangleEmbedding) ∧
                ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                    ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces)).card ≤
                      (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hEndpoint,
      a, b, faceBoundary, hv23, hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual,
      hNoResidualSelector, hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨hsynth, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary, hTait, hEndpoint,
      a, b, faceBoundary, hv23, exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary,
      hNoSelector, hNoRaw, hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector,
      hNoHeight, hNoCollar, hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

/-- Honest-source reformulation of the same endpoint-bearing nondegenerate bundled no-endpoint
wheel separation: the graph still admits theorem-4.9 synthesis for the explicit Tait coloring on
some embedding, while the fixed exact-v23 one-collar wheel shell already carries an honest
closed-walk source with a real unblocked endpoint, a concrete two-interior-edge face boundary,
and still fails every currently bundled no-endpoint repair. -/
theorem
    wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    (∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Theorem49BoundaryRootSynthesis emb wheelWithInnerTriangleTaitEdgeColoring) ∧
      ∃ source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData wheelWithInnerTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        IsTaitEdgeColoring wheelWithInnerTriangleGraph
          wheelWithInnerTriangleTaitEdgeColoring ∧
        HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding ∧
        ∃ a b : Color,
          ∃ faceBoundary : Finset wheelWithInnerTriangleGraph.edgeSet,
            Nonempty
                (V23ResidualBoundaryInitialState
                  wheelWithInnerTriangleTaitEdgeColoring a b faceBoundary) ∧
              (∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                  ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
                    e₁ ≠ e₂ ∧
                      e₁ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ∧
                      e₂ ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces) ∧
              ¬ Nonempty
                  (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) ∧
              (¬ ∃ peelFaces :
                    Finset (AmbientFace wheelWithInnerTriangleEmbedding.faces),
                  ∃ hunique :
                    PairwiseUniqueSharedInteriorEdges
                      wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces,
                  ∃ hcoverRoots : RootSetCovers
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                  ∃ hsepRoots : RootSetSeparated
                    (interiorDualGraph wheelWithInnerTriangleEmbedding.faceBoundary
                      wheelWithInnerTriangleEmbedding.faces)
                    source.boundaryFaceRoots,
                    (∀ f ∈ peelFaces,
                      Disjoint
                        (wheelWithInnerTriangleEmbedding.faceBoundary f.1)
                        (selectedBoundarySupport
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces
                          wheelWithInnerTriangleEmbedding.faces)) ∧
                    interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces ⊆
                      peelFaces.image
                        (rootedSharedInteriorEdgeOfPairwiseUnique
                          wheelWithInnerTriangleEmbedding.faceBoundary
                          wheelWithInnerTriangleEmbedding.faces hunique
                          (interiorDualSpanningForestRoot
                            wheelWithInnerTriangleEmbedding.faceBoundary
                            wheelWithInnerTriangleEmbedding.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots)
                          source.fallbackEdge)) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusRootParentPeelData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusConstructionFaceLayerData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (ResidualBoundarySelectorData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryHeightOrderedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryCollarLayerFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryWellFoundedFacePeelWitnessData
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ Nonempty
                  (PlanarBoundaryAnnulusCollarGeometry
                    wheelWithInnerTriangleEmbedding) ∧
              ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
                  ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces)).card ≤
                    (1 : ℕ) := by
  rcases
      wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry with
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩
  exact
    ⟨hsynth, source, hcurrent, hTait, hEndpoint, a, b, faceBoundary, hv23,
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary, hNoSelector, hNoRaw,
      hNoParent, hNoConstruction, hNoResidual, hNoResidualSelector, hNoHeight, hNoCollar,
      hNoWellFounded, hNoAnnulus, hNoAtMostOne⟩

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
