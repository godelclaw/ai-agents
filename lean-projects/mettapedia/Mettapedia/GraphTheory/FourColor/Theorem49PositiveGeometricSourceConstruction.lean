import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometryRegression

/-!
# Positive annulus-source construction for Theorem 4.9

This file records a concrete inhabited benchmark for the replacement positive source package:
a two-collar annulus geometry whose shared intermediate boundary edge supplies a purified
selected-boundary interior endpoint carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PositiveGeometricSourceConstruction

open Theorem49PlanarBoundaryAnnulusGeometryRegression
open Theorem49ForcingInteriorEdgeObstruction

/-- In the two-collar benchmark, the intermediate edge is exactly the face-incidence interior
edge support. -/
theorem counterEmbedding_interiorEdgeSupport_eq :
    interiorEdgeSupport counterEmbedding.faceBoundary counterEmbedding.faces = {em} := by
  ext e
  rcases edge_eq_cases e with rfl | rfl | rfl <;> decide

/-- In the two-collar benchmark, the selected ambient boundary support consists exactly of the
outer and inner boundary edges. -/
theorem counterEmbedding_selectedBoundarySupport_eq :
    selectedBoundarySupport counterEmbedding.faceBoundary counterEmbedding.faces
        counterEmbedding.faces =
      {eo, ei} := by
  ext e
  rcases edge_eq_cases e with rfl | rfl | rfl <;> decide

/-- The raw interior endpoint carrier of the two-collar benchmark is exactly the two endpoints of
the shared intermediate edge. -/
theorem counterEmbedding_interiorEdgeEndpointSupport_eq :
    interiorEdgeEndpointSupport counterEmbedding = ({2, 3} : Finset (Fin 6)) := by
  ext v
  fin_cases v <;> decide

/-- The selected-boundary endpoint support is exactly the four endpoints of the two ambient
boundary edges. -/
theorem counterEmbedding_selectedBoundaryEndpointSupport_eq :
    edgeEndpointSupport
        (selectedBoundarySupport counterEmbedding.faceBoundary counterEmbedding.faces
          counterEmbedding.faces) =
      ({0, 1, 4, 5} : Finset (Fin 6)) := by
  ext v
  fin_cases v <;> decide

/-- The raw interior endpoint carrier is disjoint from all selected-boundary endpoints in the
two-collar benchmark. -/
theorem counterEmbedding_endpointSupport_disjoint_selectedBoundarySupport :
    Disjoint (interiorEdgeEndpointSupport counterEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport counterEmbedding.faceBoundary counterEmbedding.faces
          counterEmbedding.faces)) := by
  rw [counterEmbedding_interiorEdgeEndpointSupport_eq,
    counterEmbedding_selectedBoundaryEndpointSupport_eq]
  decide

/-- The raw interior endpoint carrier is nonempty in the two-collar benchmark. -/
theorem counterEmbedding_interiorEdgeEndpointSupport_nonempty :
    (interiorEdgeEndpointSupport counterEmbedding).Nonempty := by
  rw [counterEmbedding_interiorEdgeEndpointSupport_eq]
  decide

/-- The purified selected-boundary interior endpoint carrier is exactly the raw interior endpoint
carrier in the two-collar benchmark. -/
theorem counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_eq :
    selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding =
      ({2, 3} : Finset (Fin 6)) := by
  rw [(selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
    counterEmbedding).2 counterEmbedding_endpointSupport_disjoint_selectedBoundarySupport]
  exact counterEmbedding_interiorEdgeEndpointSupport_eq

/-- In the two-collar annulus benchmark, the intermediate edge has endpoints not incident to the
selected ambient boundary, so the purified interior-edge endpoint carrier is nonempty. -/
theorem counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty :
    (selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding).Nonempty := by
  rw [counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_eq]
  decide

/-- Named local endpoint witness for the two-collar benchmark: one endpoint of the intermediate
interior edge survives selected-boundary purification. -/
theorem counterEmbedding_hasUnblockedInteriorEndpoint :
    HasUnblockedInteriorEndpoint counterEmbedding :=
  hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
    counterEmbedding_endpointSupport_disjoint_selectedBoundarySupport
    counterEmbedding_interiorEdgeEndpointSupport_nonempty

/-- The same two-collar benchmark also carries a forcing interior edge: the shared intermediate
edge `em` is interior, and each of its incident faces already contains selected-boundary support.
So forcing-edge obstruction cannot be promoted to a generic blocker for direct replacement-positive
geometry. -/
def counterEmbeddingForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness counterEmbedding where
  edge := em
  heInterior := by
    rw [counterEmbedding_interiorEdgeSupport_eq]
    simp
  hforcing := by
    intro f _hf
    rcases f with ⟨face, _hface⟩
    change CounterFace at face
    fin_cases face
    · refine ⟨eo, ?_, ?_⟩
      · simp [counterEmbedding, counterFaceBoundary]
      · rw [counterEmbedding_selectedBoundarySupport_eq]
        simp
    · refine ⟨ei, ?_, ?_⟩
      · simp [counterEmbedding, counterFaceBoundary]
      · rw [counterEmbedding_selectedBoundarySupport_eq]
        simp

theorem nonempty_forcingInteriorEdgeWitness_counterEmbedding :
    Nonempty (ForcingInteriorEdgeWitness counterEmbedding) :=
  ⟨counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The forcing witness rules out the boundary-free selector shell on the same positive benchmark.
-/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector counterEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      nonempty_forcingInteriorEdgeWitness_counterEmbedding

/-- The concrete two-collar annulus geometry inhabits the fixed-embedding finite-collar replacement
positive source package. -/
theorem counterEmbedding_collarLayerPositiveProjectedGeometryOn :
    Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry
      counterCollarGeometry
      counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty

/-- The same benchmark also inhabits the fixed-embedding height-ordered replacement source package.
-/
theorem counterEmbedding_heightOrderedPositiveProjectedGeometryOn :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry
      counterCollarGeometry
      counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty

/-- The direct replacement-positive benchmark and the forcing-edge obstruction coexist on the
same embedding.  This blocks any generic same-embedding theorem that would try to rule out
forcing interior edges from direct replacement-positive geometry alone. -/
theorem counterEmbedding_directPositiveProjectedGeometryOn_and_forcingInteriorEdgeWitness :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      Nonempty (ForcingInteriorEdgeWitness counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩

/-- The same direct replacement-positive benchmark still fails both the selector and construction
face-layer shells on the same embedding. -/
theorem
    counterEmbedding_directPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      ¬ Nonempty (BoundaryFreeIncidentFaceSelector counterEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := counterEmbedding) counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The same direct replacement-positive benchmark also fails the stronger boundary-support face
construction shell on the same embedding. -/
theorem
    counterEmbedding_directPositiveProjectedGeometryOn_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData
        (emb := counterEmbedding) counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The same direct replacement-positive benchmark also fails the intermediate face-partition
construction shell on the same embedding. -/
theorem
    counterEmbedding_directPositiveProjectedGeometryOn_without_planarBoundaryAnnulusConstructionFacePartitionData
    :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFacePartitionData counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData
        (emb := counterEmbedding) counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The same direct replacement-positive benchmark also fails the intermediate positive-frontier
construction shell on the same embedding. -/
theorem
    counterEmbedding_directPositiveProjectedGeometryOn_without_planarBoundaryAnnulusConstructionPositiveFrontierData
    :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
        (emb := counterEmbedding) counterEmbeddingForcingInteriorEdgeWitness⟩

/-- Graph-level finite-collar replacement source data for the two-collar annulus benchmark. -/
noncomputable def counterGraph_collarLayerPositiveProjectedGeometry :
    Theorem49CollarLayerPositiveProjectedGeometry counterGraph :=
  theorem49CollarLayerPositiveProjectedGeometry_of_annulusCollarGeometry
    counterCollarGeometry
    counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty

/-- Graph-level height-ordered replacement source data for the two-collar annulus benchmark. -/
noncomputable def counterGraph_heightOrderedPositiveProjectedGeometry :
    Theorem49HeightOrderedPositiveProjectedGeometry counterGraph :=
  theorem49HeightOrderedPositiveProjectedGeometry_of_annulusCollarGeometry
    counterCollarGeometry
    counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty

/-- The finite-collar replacement positive source package is genuinely inhabited by the benchmark,
not merely syntactically satisfiable as a target. -/
theorem nonempty_counterGraph_collarLayerPositiveProjectedGeometry :
    Nonempty (Theorem49CollarLayerPositiveProjectedGeometry counterGraph) := by
  exact ⟨counterGraph_collarLayerPositiveProjectedGeometry⟩

/-- The height-ordered replacement positive source package is likewise inhabited by the benchmark.
-/
theorem nonempty_counterGraph_heightOrderedPositiveProjectedGeometry :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry counterGraph) := by
  exact ⟨counterGraph_heightOrderedPositiveProjectedGeometry⟩

/-- The two-collar benchmark graph already has a same-embedding model carrying both direct
replacement-positive predicates and a forcing interior edge. -/
theorem
    exists_embedding_directPositiveProjectedGeometryOn_and_forcingInteriorEdgeWitness_counterGraph
    :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
        Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact ⟨counterEmbedding,
    counterEmbedding_directPositiveProjectedGeometryOn_and_forcingInteriorEdgeWitness⟩

/-- Therefore direct height-ordered replacement geometry does not universally exclude forcing
interior edges on one embedding. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_theorem49HeightOrderedPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb => Theorem49HeightOrderedPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩

/-- The same failure already holds for finite-collar replacement geometry itself. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_theorem49CollarLayerPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49CollarLayerPositiveProjectedGeometryOn emb →
          ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb => Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        counterEmbedding_collarLayerPositiveProjectedGeometryOn,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩

/-- Even the conjunction of the two direct replacement-positive predicates does not universally
exclude forcing interior edges on one embedding. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Direct replacement-positive geometry does not universally produce a boundary-free selector on
the same embedding. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  refine
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Direct replacement-positive geometry does not universally produce the stronger
boundary-support-face construction shell on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Direct replacement-positive geometry does not universally produce the intermediate
face-partition construction shell on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Direct replacement-positive geometry does not universally produce the intermediate
positive-frontier construction shell on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Direct replacement-positive geometry also does not universally produce the downstream
construction face-layer package on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_directPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb →
          Theorem49CollarLayerPositiveProjectedGeometryOn emb →
            Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (G := counterGraph)
      (P := fun emb =>
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb)
      ⟨counterEmbedding,
        ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
          counterEmbedding_collarLayerPositiveProjectedGeometryOn⟩,
        nonempty_forcingInteriorEdgeWitness_counterEmbedding⟩
      ?_
  intro emb hpair
  exact h hpair.1 hpair.2

/-- Minimal graph-level hypotheses behind the concrete positive replacement benchmark: an
annulus collar geometry on the two-collar embedding and a surviving purified carrier. -/
theorem exists_counterGraph_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  exact
    ⟨counterEmbedding, counterCollarGeometry,
      counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty⟩

/-- A constant nonzero Tait coloring of the two-collar annulus benchmark.  The graph has three
pairwise disjoint edges, so the line-graph properness condition is vacuous. -/
def counterGraphTaitEdgeColoring : counterGraph.EdgeColoring Color :=
  Coloring.mk (fun _ => red) (by
    intro e f hadj
    rcases edge_eq_cases e with rfl | rfl | rfl <;>
      rcases edge_eq_cases f with rfl | rfl | rfl <;>
      simp [SimpleGraph.lineGraph_adj_iff_exists, counterGraph, eo,
        Theorem49PlanarBoundaryAnnulusGeometryRegression.em, ei] at hadj ⊢)

theorem counterGraphTaitEdgeColoring_isTait :
    IsTaitEdgeColoring counterGraph counterGraphTaitEdgeColoring := by
  intro e
  change red ≠ 0
  exact red_ne_zero

/-- The concrete two-collar benchmark reaches the fixed-embedding nonempty projected synthesis
endpoint from its explicit collar geometry, surviving purified carrier, and Tait coloring. -/
theorem counterEmbedding_boundaryRootNonemptyProjectedSynthesis
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    Theorem49BoundaryRootNonemptyProjectedSynthesis
      counterEmbedding counterGraphTaitEdgeColoring := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
      counterCollarGeometry
      counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait

/-- End-to-end nonvacuous calibration for the concrete two-collar benchmark.  The actual collar
geometry, explicit Tait coloring, and surviving purified carrier reach the projected theorem-4.9
endpoint and therefore provide the raw Definition 4.8 representative plus selected-boundary
kernel error decomposition for every Kirchhoff chain on the same embedding. -/
theorem counterEmbedding_collarGeometry_explicitTait_nonemptyCarrier_to_theorem49RawQuotientErrorPackage
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusCollarGeometry counterEmbedding) ∧
      IsTaitEdgeColoring counterGraph counterGraphTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding).Nonempty ∧
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        counterEmbedding counterGraphTaitEdgeColoring ∧
      ∀ x : counterGraph.edgeSet → Color,
        x ∈
            kirchhoffSubmodule counterGraph
              (selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding) →
          Theorem49BoundaryRawQuotientErrorPackage counterEmbedding
            counterGraphTaitEdgeColoring x := by
  refine
    ⟨⟨counterCollarGeometry⟩,
      counterGraphTaitEdgeColoring_isTait,
      counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty,
      counterEmbedding_boundaryRootNonemptyProjectedSynthesis, ?_⟩
  intro x hx
  exact
    counterEmbedding_boundaryRootNonemptyProjectedSynthesis
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The unique matching partner of a vertex in the two-collar benchmark graph. -/
def counterMate (v : Fin 6) : Fin 6 :=
  match v.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | _ => 0

/-- Every neighbor in the two-collar benchmark graph is the matching partner. -/
theorem counterGraph_adj_left_eq_counterMate {u v : Fin 6}
    (h : counterGraph.Adj u v) : u = counterMate v := by
  let e : counterGraph.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet counterGraph).2 h⟩
  rcases edge_eq_cases e with he | he | he
  · have hval : s(u, v) = s(0, 1) := by
      simpa [e, eo] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(2, 3) := by
      simpa [e, Theorem49PlanarBoundaryAnnulusGeometryRegression.em] using
        congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(4, 5) := by
      simpa [e, ei] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- Two consecutive edges in the two-collar benchmark matching return to the starting vertex. -/
theorem counterGraph_adj_adj_eq {a b c : Fin 6}
    (hab : counterGraph.Adj a b) (hbc : counterGraph.Adj b c) : a = c :=
  (counterGraph_adj_left_eq_counterMate hab).trans
    (counterGraph_adj_left_eq_counterMate hbc.symm).symm

/-- A trail in the two-collar benchmark matching has length at most one. -/
theorem counterGraph_walk_length_le_one {v w : Fin 6}
    (p : counterGraph.Walk v w) (htrail : p.IsTrail) : p.length ≤ 1 := by
  cases p with
  | nil => simp
  | cons h1 p1 =>
      cases p1 with
      | nil => simp
      | cons h2 p2 =>
          exfalso
          have hnodup :
              (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p2)).edges.Nodup := by
            simpa [SimpleGraph.Walk.isTrail_def] using htrail
          have hx := counterGraph_adj_adj_eq h1 h2
          simp [SimpleGraph.Walk.edges_cons, hx] at hnodup

/-- The two-collar benchmark graph is a finite matching, hence acyclic. -/
theorem counterGraph_isAcyclic : counterGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 1 := counterGraph_walk_length_le_one c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  omega

/-- The two-collar benchmark graph has a nonempty edge set. -/
theorem counterGraph_edgeSet_nonempty : Nonempty counterGraph.edgeSet :=
  ⟨eo⟩

/-- The concrete two-collar embedding cannot be promoted to an honest closed-walk annulus source.
Its graph is only a matching, so every nonempty facial closed trail would contradict acyclicity.
-/
theorem not_nonempty_closedWalkAnnulusBoundarySource_counterEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource counterEmbedding) := by
  exact
    not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      counterGraph_isAcyclic counterGraph_edgeSet_nonempty

/-- Graph-level form of the same source-side obstruction for the two-collar benchmark graph. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_counterGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource counterGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      counterGraph_isAcyclic counterGraph_edgeSet_nonempty

/-- Calibration of the concrete two-collar benchmark: it reaches the nonempty raw theorem-4.9
quotient/error package from explicit collar geometry, Tait coloring, and carrier data, but the
same fixed embedding is still not an honest closed-walk annulus source. -/
theorem counterEmbedding_rawQuotientErrorPackage_without_closedWalkAnnulusBoundarySource
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    (Nonempty (PlanarBoundaryAnnulusCollarGeometry counterEmbedding) ∧
        IsTaitEdgeColoring counterGraph counterGraphTaitEdgeColoring ∧
        (selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding).Nonempty ∧
        Theorem49BoundaryRootNonemptyProjectedSynthesis
          counterEmbedding counterGraphTaitEdgeColoring ∧
        ∀ x : counterGraph.edgeSet → Color,
          x ∈
              kirchhoffSubmodule counterGraph
                (selectedBoundaryInteriorEdgeEndpointVertices counterEmbedding) →
            Theorem49BoundaryRawQuotientErrorPackage counterEmbedding
              counterGraphTaitEdgeColoring x) ∧
      ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource counterEmbedding) := by
  exact
    ⟨counterEmbedding_collarGeometry_explicitTait_nonemptyCarrier_to_theorem49RawQuotientErrorPackage,
      not_nonempty_closedWalkAnnulusBoundarySource_counterEmbedding⟩

/-- Stronger calibration of the two-collar benchmark: it reaches the nonempty projected endpoint
through repaired previous-boundary witness geometry and an explicit unblocked endpoint, but the
canonical annulus construction on that same collar still fails parent-witness orientation. -/
theorem counterEmbedding_previousBoundaryWitness_nonemptyProjectedSynthesis_without_parentWitnessOrientation
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry counterEmbedding) ∧
      HasUnblockedInteriorEndpoint counterEmbedding ∧
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        counterEmbedding counterGraphTaitEdgeColoring ∧
      ¬ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
            counterPreviousBoundaryWitnessGeometry.toPlanarBoundaryAnnulusCollarGeometry
          ).ParentWitnessOrientation := by
  exact
    ⟨⟨counterPreviousBoundaryWitnessGeometry⟩,
      counterEmbedding_hasUnblockedInteriorEndpoint,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry
        counterPreviousBoundaryWitnessGeometry
        counterEmbedding_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait,
      by
        simpa [counterConstruction, counterPreviousBoundaryWitnessGeometry] using
          not_counterConstructionParentWitnessOrientation⟩

/-- On the concrete two-collar benchmark, the projected theorem-4.9 endpoint already coexists on
the same embedding with both direct replacement-positive predicates, a forcing interior edge, and
failure of the selector and construction face-layer shells. -/
theorem
    counterEmbedding_directPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    Theorem49HeightOrderedPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49CollarLayerPositiveProjectedGeometryOn counterEmbedding ∧
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        counterEmbedding counterGraphTaitEdgeColoring ∧
      Nonempty (ForcingInteriorEdgeWitness counterEmbedding) ∧
      ¬ Nonempty (BoundaryFreeIncidentFaceSelector counterEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData counterEmbedding) := by
  exact
    ⟨counterEmbedding_heightOrderedPositiveProjectedGeometryOn,
      counterEmbedding_collarLayerPositiveProjectedGeometryOn,
      counterEmbedding_boundaryRootNonemptyProjectedSynthesis,
      nonempty_forcingInteriorEdgeWitness_counterEmbedding,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := counterEmbedding) counterEmbeddingForcingInteriorEdgeWitness⟩

/-- Graph-level existential form of the concrete positive replacement route for the two-collar
annulus benchmark. -/
theorem exists_counterGraph_boundaryRootNonemptyProjectedSynthesis
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        emb counterGraphTaitEdgeColoring := by
  exact
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      exists_counterGraph_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait

/-- Graph-level classification of the concrete two-collar positive benchmark: the graph already
inhabits the direct replacement packages and reaches the explicit nonempty projected theorem-4.9
endpoint for its constant Tait coloring, but it still cannot arise from an honest closed-walk
annulus source. -/
theorem
    counterGraph_explicitTait_positiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_without_closedWalkAnnulusBoundarySource
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    IsTaitEdgeColoring counterGraph counterGraphTaitEdgeColoring ∧
      Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry counterGraph) ∧
      Nonempty (Theorem49CollarLayerPositiveProjectedGeometry counterGraph) ∧
      (∃ emb : PlaneEmbeddingWithBoundary counterGraph,
        Theorem49BoundaryRootNonemptyProjectedSynthesis
          emb counterGraphTaitEdgeColoring) ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource counterGraph := by
  exact
    ⟨counterGraphTaitEdgeColoring_isTait,
      nonempty_counterGraph_heightOrderedPositiveProjectedGeometry,
      nonempty_counterGraph_collarLayerPositiveProjectedGeometry,
      exists_counterGraph_boundaryRootNonemptyProjectedSynthesis,
      not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_counterGraph⟩

/-- Stronger graph-level classification of the same benchmark: for the explicit Tait coloring, the
current direct positive packages and the projected theorem-4.9 endpoint already coexist on one
embedding with a forcing interior edge and failure of the selector and construction face-layer
shells.  So this branch is not merely off the honest-source route; it also does not supply the
currently needed same-embedding selector/construction geometry. -/
theorem
    counterGraph_explicitTait_positiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype counterGraph.edgeSet] [FiniteDimensional F2 (counterGraph.edgeSet → Color)] :
    IsTaitEdgeColoring counterGraph counterGraphTaitEdgeColoring ∧
      Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry counterGraph) ∧
      Nonempty (Theorem49CollarLayerPositiveProjectedGeometry counterGraph) ∧
      (∃ emb : PlaneEmbeddingWithBoundary counterGraph,
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
          Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
          Theorem49BoundaryRootNonemptyProjectedSynthesis
            emb counterGraphTaitEdgeColoring ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
  exact
    ⟨counterGraphTaitEdgeColoring_isTait,
      nonempty_counterGraph_heightOrderedPositiveProjectedGeometry,
      nonempty_counterGraph_collarLayerPositiveProjectedGeometry,
      ⟨counterEmbedding,
        counterEmbedding_directPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData⟩⟩

end Theorem49PositiveGeometricSourceConstruction

end Mettapedia.GraphTheory.FourColor
