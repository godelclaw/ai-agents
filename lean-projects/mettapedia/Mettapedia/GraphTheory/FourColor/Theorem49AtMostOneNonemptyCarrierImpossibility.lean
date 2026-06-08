import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

/-!
# Route impossibility: at-most-one does not guarantee nonempty carrier

This file started as a counterexample module showing that the
at-most-one-interior-edge-per-face condition does not guarantee that the
`selectedBoundaryInteriorEdgeEndpointVertices` carrier is nonempty.  It now proves the sharper
diagnosis for honest cyclic facial boundary data: closed-walk face boundaries plus facewise
at-most-one actually force that purified carrier to be empty.

## Counterexample

The chained-diamonds-with-triangle graph serves as a counterexample:

1. It admits a cyclic source (closed walk annulus boundary source)
2. It satisfies at-most-one-interior-edge-per-face
3. But its carrier is EMPTY

The concrete examples establish route impossibility for the second attempted derivation:
  at-most-one + cyclic source ↛ nonempty carrier

The structural theorems below strengthen this to:
  honest closed-walk source + at-most-one → empty purified carrier

## Implications

The current successor/closed-walk at-most-one non-vacuous synthesis wrappers therefore have
inconsistent geometric hypotheses unless the carrier, at-most-one premise, or source geometry is
changed.  The nonempty carrier condition is not merely underived on this branch; it is
incompatible with the current honest cyclic at-most-one source shell.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
open Theorem49InteriorVerticesEndpointObstruction

/-!
### Route impossibility theorem

The chained-diamonds regression proves that at-most-one-interior-edge-per-face
does NOT imply nonempty selectedBoundaryInteriorEdgeEndpointVertices.
-/

theorem route_impossibility_at_most_one_does_not_imply_nonempty_carrier :
    ∃ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  use chainedDiamondsWithTriangleGraph, chainedDiamondsWithTriangleEmbedding
  exact
    ⟨chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle⟩

/-- A universal derivation of nonempty selected-boundary purified carrier from the local
at-most-one condition is false, even on the fixed `Fin 10` vertex type: the chained-diamonds
embedding satisfies at-most-one on every face while the purified carrier is empty. -/
theorem not_forall_atMostOneInteriorEdgePerFace_implies_nonempty_carrier :
    ¬ ∀ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro h
  exact
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle
      (h chainedDiamondsWithTriangleGraph chainedDiamondsWithTriangleEmbedding
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace)

/-!
### Why empty carriers are possible

The carrier `selectedBoundaryInteriorEdgeEndpointVertices` contains vertices that
are endpoints of interior edges but NOT endpoints of selected boundary edges.

Even if each face has at most one interior edge, it's possible for ALL interior
edge endpoints to also be endpoints of selected boundary edges, making the
carrier empty.

In the chained-diamonds example:
- Each face has at most one interior edge (satisfies at-most-one)
- But every vertex that's an endpoint of an interior edge is ALSO an endpoint
  of a selected boundary edge
- So the "purified" carrier (interior endpoints NOT on selected boundary) is empty

This shows that at-most-one is about face-local structure (how many interior
edges per face), while nonempty carrier is about global vertex-edge incidence
structure (which vertices are "purely interior" vs "boundary-adjacent").

These are independent geometric conditions.
-/

theorem at_most_one_and_empty_carrier_independent :
    ∃ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  use chainedDiamondsWithTriangleGraph, chainedDiamondsWithTriangleEmbedding
  exact
    ⟨⟨chainedDiamondsClosedWalkAnnulusBoundarySource⟩,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle⟩

/-- Even adding the honest closed-walk annulus boundary source does not make the local at-most-one
condition imply nonempty purified carrier. -/
theorem
    not_forall_closedWalkSource_and_atMostOneInteriorEdgePerFace_implies_nonempty_carrier :
    ¬ ∀ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro h
  exact
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle
      (h chainedDiamondsWithTriangleGraph chainedDiamondsWithTriangleEmbedding
        ⟨chainedDiamondsClosedWalkAnnulusBoundarySource⟩
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace)

/-!
### Strengthened successor-cycle source exposes a stronger empty-carrier obstruction

The smaller diamond-with-triangle model has a genuine successor-cycle boundary source and
satisfies facewise at-most-one, but the purified carrier is empty.  The universal theorem below
shows that this is not an accidental finite example: with the current purified-carrier definition,
successor-cycle facial data plus facewise at-most-one forces the carrier to be empty.
-/

def diamondWithTriangleFace0DartSuccessor (d : diamondWithTriangleGraph.Dart) :
    diamondWithTriangleGraph.Dart :=
  if d = dtDart20 then dtDart01
  else if d = dtDart01 then dtDart12
  else dtDart20

def diamondWithTriangleFace1DartSuccessor (d : diamondWithTriangleGraph.Dart) :
    diamondWithTriangleGraph.Dart :=
  if d = dtDart23 then dtDart31
  else if d = dtDart31 then dtDart12
  else dtDart23

def diamondWithTriangleFace2DartSuccessor (d : diamondWithTriangleGraph.Dart) :
    diamondWithTriangleGraph.Dart :=
  if d = dtDart45 then dtDart56
  else if d = dtDart56 then dtDart64
  else dtDart45

def diamondWithTriangleFace0DartSuccessorCycle
    (hf : (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      diamondWithTriangleEmbedding ⟨(0 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart20, dtDart01, dtDart12]
  hnonempty := by simp
  successor := diamondWithTriangleFace0DartSuccessor
  hsuccessor_order := by
    simp [diamondWithTriangleFace0DartSuccessor, dtDart20, dtDart01, dtDart12]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, diamondWithTriangleFace0DartSuccessor,
        dtDart20, dtDart01, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (diamondWithTriangleFace0SelectedArcPureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (diamondWithTriangleFace0SelectedArcPureDartCycle hf).hface_sub e he

def diamondWithTriangleFace1DartSuccessorCycle
    (hf : (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      diamondWithTriangleEmbedding ⟨(1 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart23, dtDart31, dtDart12]
  hnonempty := by simp
  successor := diamondWithTriangleFace1DartSuccessor
  hsuccessor_order := by
    simp [diamondWithTriangleFace1DartSuccessor, dtDart23, dtDart31, dtDart12]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, diamondWithTriangleFace1DartSuccessor,
        dtDart23, dtDart31, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (diamondWithTriangleFace1SelectedArcPureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (diamondWithTriangleFace1SelectedArcPureDartCycle hf).hface_sub e he

def diamondWithTriangleFace2DartSuccessorCycle
    (hf : (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      diamondWithTriangleEmbedding ⟨(2 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart45, dtDart56, dtDart64]
  hnonempty := by simp
  successor := diamondWithTriangleFace2DartSuccessor
  hsuccessor_order := by
    simp [diamondWithTriangleFace2DartSuccessor, dtDart45, dtDart56, dtDart64]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, diamondWithTriangleFace2DartSuccessor,
        dtDart45, dtDart56, dtDart64]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (diamondWithTriangleFace2PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (diamondWithTriangleFace2PureDartCycle hf).hface_sub e he

def diamondWithTriangleDartSuccessorCycleGeometry :
    PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding where
  faceBoundaryDartSuccessorCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondWithTriangleFace at f
    by_cases h0 : f = (0 : DiamondWithTriangleFace)
    · subst f
      exact diamondWithTriangleFace0DartSuccessorCycle hfmem
    · by_cases h1 : f = (1 : DiamondWithTriangleFace)
      · subst f
        exact diamondWithTriangleFace1DartSuccessorCycle hfmem
      · have h2 : f = (2 : DiamondWithTriangleFace) := by
          rcases f with ⟨n, hn⟩
          have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
          rcases hn012 with rfl | rfl | rfl
          · exact False.elim (h0 rfl)
          · exact False.elim (h1 rfl)
          · rfl
        subst f
        exact diamondWithTriangleFace2DartSuccessorCycle hfmem

theorem diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      (diamondWithTriangleDartSuccessorCycleGeometry
        |>.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  intro f
  let f0 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(0 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  let f1 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(1 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  let f2 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(2 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  have hf_cases : f = f0 ∨ f = f1 ∨ f = f2 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn012 with rfl | rfl | rfl
    · left
      exact Subtype.ext rfl
    · right
      left
      exact Subtype.ext rfl
    · right
      right
      exact Subtype.ext rfl
  rcases hf_cases with rfl | rfl | rfl
  · change
      (diamondWithTriangleDartSuccessorCycleGeometry
        |>.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f0
    refine ⟨[dt02, dt01], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleDartSuccessorCycleGeometry
        |>.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f1
    refine ⟨[dt23, dt13], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleDartSuccessorCycleGeometry
        |>.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f2
    refine ⟨[dt45, dt56, dt64], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem successor_cycle_at_most_one_and_empty_carrier_independent :
    ∃ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
          selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
            ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  exact
    ⟨diamondWithTriangleGraph, diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource.boundaryReachability,
      diamondWithTriangleDartSuccessorCycleGeometry,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- The diamond benchmark concretely inhabits the live successor-cycle source shell together
with the facewise at-most-one local criterion.  This packages the exact hypothesis surface used
by the new direct witness-assignment and theorem-4.9 route theorems. -/
theorem
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ) := by
  exact
    ⟨diamondWithTriangleEmbedding, diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleDartSuccessorCycleGeometry,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      diamondWithTriangle_atMostOneInteriorEdgePerFace⟩

/-- The live successor-cycle plus facewise-at-most-one route is already genuinely inhabited:
the diamond benchmark reaches split-annulus witness assignment directly on that shell, before any
nonempty-carrier upgrade is attempted. -/
theorem
    diamondWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_successorCycle_facewiseAtMostOneInteriorEdge :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment diamondWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_diamondWithTriangleGraph

/-- The same live-shell package also reaches the explicit theorem-4.9 endpoint on the Tait-colored
diamond benchmark.  This shows the successor-cycle facewise-at-most-one route is constructive in
practice; the remaining blocker on this branch is the nonempty-carrier upgrade, not basic
Theorem-4.9 reachability. -/
theorem
    exists_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_facewiseAtMostOneInteriorEdge
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Theorem49BoundaryRootSynthesis emb diamondWithTriangleTaitEdgeColoring := by
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- The constructive diamond benchmark already inhabits the exact successor-cycle one-collar
current-boundary shell.  On that same live shell, facewise at-most-one still holds, the canonical
one-collar annulus witness assignment is nonempty, and the explicit Tait coloring already reaches
full theorem-4.9 synthesis on the fixed embedding.  So on this positive branch the exact current-
boundary shell is not the missing burden. -/
theorem
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)) ∧
        ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring diamondWithTriangleGraph C ∧
            Theorem49BoundaryRootSynthesis emb C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleDartSuccessorCycleGeometry,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace⟩

/-- The same live successor-cycle benchmark also carries the stronger fallback/count/boundary-rest
surface used by the direct projected Definition 4.8 route theorems. -/
theorem
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → diamondWithTriangleGraph.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : diamondWithTriangleGraph.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  exact
    ⟨diamondWithTriangleEmbedding, diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleDartSuccessorCycleGeometry,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      diamondWithTriangleFallbackEdge, diamondWithTriangleFallbackEdge_mem,
      diamondWithTriangle_atMostOneInteriorEdgePerFace, by
        simpa [diamondWithTriangleClosedWalkAnnulusBoundarySource] using
          diamondWithTriangle_nonInteriorOnAmbient⟩

/-- The same explicit diamond benchmark also carries the honest closed-walk source plus the
fallback/count/boundary-rest surface used by the direct projected Definition 4.8 route theorems.
-/
theorem
    exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → diamondWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : diamondWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  exact
    ⟨diamondWithTriangleEmbedding, diamondWithTriangleClosedWalkAnnulusBoundarySource,
      diamondWithTriangleFallbackEdge, diamondWithTriangleFallbackEdge_mem,
      diamondWithTriangle_atMostOneInteriorEdgePerFace, by
        simpa [diamondWithTriangleClosedWalkAnnulusBoundarySource] using
          diamondWithTriangle_nonInteriorOnAmbient⟩

/-- The explicit Tait-colored diamond benchmark reaches the corrected projected Definition 4.8
subspace statement directly on the live successor-cycle at-most-one shell. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- The same concrete shell also reaches the family-level projected spanning statement. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb diamondWithTriangleTaitEdgeColoring) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- The same explicit shell also reaches the first chain-dot duality endpoint on the natural
purified carrier vertex set. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
              (chainDotBilinForm diamondWithTriangleGraph.edgeSet).orthogonal
                (projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring) =
            ⊥ := by
  rcases
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hbot⟩
  exact ⟨emb, ⟨data⟩, hbot⟩

/-- The pointwise chain-dot orthogonality characterization also holds on that same explicit live
successor-cycle shell. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ z :
              theorem49BoundaryZeroKirchhoffSubspace emb
                (selectedBoundaryInteriorEdgeEndpointVertices emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring,
              chainDotBilinForm diamondWithTriangleGraph.edgeSet p
                  (z : diamondWithTriangleGraph.edgeSet → Color) =
                0) ↔
              z = 0 := by
  rcases
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hzero⟩
  exact ⟨emb, ⟨data⟩, hzero⟩

/-- The same explicit live shell also reaches the raw finite Definition 4.8 generator-sum
representation on the natural purified carrier vertex set. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ {z : diamondWithTriangleGraph.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ (coeff : (diamondWithTriangleGraph.edgeSet → Color) → F2)
                (terms : Finset (diamondWithTriangleGraph.edgeSet → Color)),
              (terms : Set (diamondWithTriangleGraph.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary diamondWithTriangleTaitEdgeColoring ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hsum⟩
  exact ⟨emb, ⟨data⟩, hsum⟩

/-- The same explicit live shell also reaches the nonzero projected-generator detector on the
natural purified carrier vertex set. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ z :
              theorem49BoundaryZeroKirchhoffSubspace emb
                (selectedBoundaryInteriorEdgeEndpointVertices emb),
            z ≠ 0 →
              ∃ p ∈ projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring,
                chainDotBilinForm diamondWithTriangleGraph.edgeSet p
                    (z : diamondWithTriangleGraph.edgeSet → Color) ≠
                  0 := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hdetect⟩
  exact ⟨emb, ⟨data⟩, hdetect⟩

/-- The explicit Tait-colored diamond benchmark reaches the corrected projected Definition 4.8
subspace statement directly on the honest closed-walk at-most-one shell as well. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- The same honest-source shell also reaches the family-level projected spanning statement. -/
theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb diamondWithTriangleTaitEdgeColoring) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- The same honest-source shell also reaches the first chain-dot duality endpoint on the natural
purified carrier vertex set. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
              (chainDotBilinForm diamondWithTriangleGraph.edgeSet).orthogonal
                (projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring) =
            ⊥ := by
  rcases
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hbot⟩
  exact ⟨emb, ⟨data⟩, hbot⟩

/-- The pointwise chain-dot orthogonality characterization also holds on that same explicit honest
closed-walk shell. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ z :
              theorem49BoundaryZeroKirchhoffSubspace emb
                (selectedBoundaryInteriorEdgeEndpointVertices emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring,
              chainDotBilinForm diamondWithTriangleGraph.edgeSet p
                  (z : diamondWithTriangleGraph.edgeSet → Color) =
                0) ↔
              z = 0 := by
  rcases
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hzero⟩
  exact ⟨emb, ⟨data⟩, hzero⟩

/-- The same explicit honest-source shell also reaches the raw finite Definition 4.8 generator-sum
representation on the natural purified carrier vertex set. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ {z : diamondWithTriangleGraph.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ (coeff : (diamondWithTriangleGraph.edgeSet → Color) → F2)
                (terms : Finset (diamondWithTriangleGraph.edgeSet → Color)),
              (terms : Set (diamondWithTriangleGraph.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary diamondWithTriangleTaitEdgeColoring ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hsum⟩
  exact ⟨emb, ⟨data⟩, hsum⟩

/-- The same explicit honest-source shell also reaches the nonzero projected-generator detector on
the natural purified carrier vertex set. -/
theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        ∀ z :
              theorem49BoundaryZeroKirchhoffSubspace emb
                (selectedBoundaryInteriorEdgeEndpointVertices emb),
            z ≠ 0 →
              ∃ p ∈ projectedKempeClosureGeneratorSubspace emb diamondWithTriangleTaitEdgeColoring,
                chainDotBilinForm diamondWithTriangleGraph.edgeSet p
                    (z : diamondWithTriangleGraph.edgeSet → Color) ≠
                  0 := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait
      (fun emb _ => selectedBoundaryInteriorEdgeEndpointVertices emb) with
    ⟨emb, data, hdetect⟩
  exact ⟨emb, ⟨data⟩, hdetect⟩

/-- The diamond-with-triangle embedding is also a finite countermodel to deriving the current
boundary-root interior-dual distance package from the raw successor-cycle source shell. -/
theorem not_forall_successorCycleSource_implies_interiorDualRootDistance_diamondWithTriangle :
    ¬ ∀ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  intro h
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle
    (h diamondWithTriangleGraph diamondWithTriangleEmbedding
      diamondWithTriangleClosedWalkAnnulusBoundarySource.boundaryReachability
      diamondWithTriangleDartSuccessorCycleGeometry
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace)

/-- Even the route-facing successor-cycle source shell plus facewise at-most-one does not imply
that the purified selected-boundary interior carrier is nonempty. -/
theorem
    not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_implies_nonempty_carrier :
    ¬ ∀ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro h
  exact
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
      (h diamondWithTriangleGraph diamondWithTriangleEmbedding
        diamondWithTriangleClosedWalkAnnulusBoundarySource.boundaryReachability
        diamondWithTriangleDartSuccessorCycleGeometry
        diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        diamondWithTriangle_atMostOneInteriorEdgePerFace)

/-!
### Universal obstruction behind the successor-cycle counterexample

The concrete diamond model is not an accident.  Once every face carries a genuine
successor-cycle dart boundary, a face-local at-most-one interior-edge condition
forces every endpoint of every interior edge to be incident to a selected
boundary edge.  Hence the purified endpoint carrier is empty.
-/

private theorem successor_mem_of_forall₂_successor_order {α : Type*}
    (succ : α → α) :
    ∀ {xs ys : List α},
      List.Forall₂ (fun x y => succ x = y) xs ys →
        ∀ {x : α}, x ∈ xs → succ x ∈ ys
  | [], [], _, _, hx => by cases hx
  | x :: xs, y :: ys, hxy, z, hz => by
      cases hxy with
      | cons hxy htail =>
          rcases (by simpa using hz : z = x ∨ z ∈ xs) with rfl | hz'
          · simp [hxy]
          · simp [successor_mem_of_forall₂_successor_order succ htail hz']

private theorem exists_predecessor_of_forall₂_successor_order {α : Type*}
    (succ : α → α) :
    ∀ {xs ys : List α},
      List.Forall₂ (fun x y => succ x = y) xs ys →
        ∀ {y : α}, y ∈ ys → ∃ x ∈ xs, succ x = y
  | [], [], _, _, hy => by cases hy
  | x :: xs, y :: ys, hxy, z, hz => by
      cases hxy with
      | cons hxy htail =>
          rcases (by simpa using hz : z = y ∨ z ∈ ys) with rfl | hz'
          · exact ⟨x, by simp, hxy⟩
          · rcases exists_predecessor_of_forall₂_successor_order succ htail hz' with
              ⟨w, hw, hsucc⟩
            exact ⟨w, by simp [hw], hsucc⟩

private theorem mem_tail_append_head_toList_subset {α : Type*} {xs : List α} {x : α} :
    x ∈ xs.tail ++ xs.head?.toList → x ∈ xs := by
  cases xs with
  | nil => simp
  | cons a as => simp [or_comm]

private theorem mem_tail_append_head_toList_of_mem {α : Type*} {xs : List α}
    (hne : xs ≠ []) {x : α} (hx : x ∈ xs) :
    x ∈ xs.tail ++ xs.head?.toList := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a as =>
      rcases (by simpa using hx : x = a ∨ x ∈ as) with rfl | hx'
      · simp
      · simp [hx']

private theorem exists_right_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β},
      List.Forall₂ R xs ys → ∀ {x : α}, x ∈ xs → ∃ y ∈ ys, R x y
  | [], [], _, _, hx => by cases hx
  | x :: xs, y :: ys, hxy, z, hz => by
      cases hxy with
      | cons hxy htail =>
          rcases (by simpa using hz : z = x ∨ z ∈ xs) with rfl | hz'
          · exact ⟨y, by simp, hxy⟩
          · rcases exists_right_of_forall₂ htail hz' with ⟨w, hw, hzw⟩
            exact ⟨w, by simp [hw], hzw⟩

private theorem exists_left_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β},
      List.Forall₂ R xs ys → ∀ {y : β}, y ∈ ys → ∃ x ∈ xs, R x y
  | [], [], _, _, hy => by cases hy
  | x :: xs, y :: ys, hxy, z, hz => by
      cases hxy with
      | cons hxy htail =>
          rcases (by simpa using hz : z = y ∨ z ∈ ys) with rfl | hz'
          · exact ⟨x, by simp, hxy⟩
          · rcases exists_left_of_forall₂ htail hz' with ⟨w, hw, hwz⟩
            exact ⟨w, by simp [hw], hwz⟩

private theorem dart_mem_faceBoundary_of_mem_successor_cycle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f)
    {d : G.Dart} (hd : d ∈ cycle.darts) :
    (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ emb.faceBoundary f.1 := by
  exact
    (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk.edge_mem_faceBoundary_image_iff
      (emb := emb) (f := f) (e := ⟨d.edge, d.edge_mem⟩)).1
      (by simpa using cycle.hedge_sub d hd)

private theorem successor_mem_darts_of_mem_successor_cycle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f)
    {d : G.Dart} (hd : d ∈ cycle.darts) :
    cycle.successor d ∈ cycle.darts := by
  exact mem_tail_append_head_toList_subset <|
    successor_mem_of_forall₂_successor_order cycle.successor
      cycle.hsuccessor_order hd

private theorem edge_ne_of_successor_eq_in_successor_cycle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f)
    {p d : G.Dart} (hp : p ∈ cycle.darts) (hd : d ∈ cycle.darts)
    (hpd : cycle.successor p = d) :
    p.edge ≠ d.edge := by
  intro hedge
  have hpdart : p = d :=
    List.inj_on_of_nodup_map cycle.hnodup_edges hp hd hedge
  have hloop : p.snd = p.fst := by
    have hadj := cycle.hsuccessor_adj p hp
    have hloop0 : p.snd = (cycle.successor p).fst := by
      simpa [SimpleGraph.DartAdj] using hadj
    have hsucc_self : cycle.successor p = p := hpd.trans hpdart.symm
    rw [hsucc_self] at hloop0
    exact hloop0
  exact p.snd_ne_fst hloop

private theorem successor_edge_ne_in_successor_cycle
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f)
    {d : G.Dart} (hd : d ∈ cycle.darts) :
    (cycle.successor d).edge ≠ d.edge := by
  have hsucc_mem : cycle.successor d ∈ cycle.darts :=
    successor_mem_darts_of_mem_successor_cycle cycle hd
  exact
    (edge_ne_of_successor_eq_in_successor_cycle cycle hd hsucc_mem rfl).symm

private theorem closedWalk_dart_run_closed
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.IsChain G.DartAdj (walk.walk.darts ++ walk.walk.darts.head?.toList) := by
  have hnil := walk.walk_not_nil
  have hdartsNil : walk.walk.darts ≠ [] := by
    simpa [SimpleGraph.Walk.darts_eq_nil] using hnil
  have hfirst :
      walk.walk.darts.head? = some (walk.walk.firstDart hnil) := by
    rw [List.head?_eq_some_head hdartsNil, walk.walk.firstDart_eq_head_darts hnil]
  have hlast :
      walk.walk.darts.getLast? = some (walk.walk.lastDart hnil) := by
    rw [List.getLast?_eq_getLast_of_ne_nil hdartsNil,
      walk.walk.getLast_darts_eq_lastDart hdartsNil]
  have hheadChain : List.IsChain G.DartAdj walk.walk.darts.head?.toList := by
    simp [hfirst]
  refine walk.walk.isChain_dartAdj_darts.append hheadChain ?_
  intro x hx y hy
  have hx' : walk.walk.lastDart hnil = x := by
    simpa [hlast, Option.mem_def] using hx
  have hy' : walk.walk.firstDart hnil = y := by
    simpa [hfirst, Option.mem_def] using hy
  subst x
  subst y
  simp [SimpleGraph.DartAdj]

private theorem forall₂_dartAdj_tail_append_head_toList_of_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.Forall₂ G.DartAdj walk.walk.darts
      (walk.walk.darts.tail ++ walk.walk.darts.head?.toList) := by
  cases hds : walk.walk.darts with
  | nil =>
      simp
  | cons d ds =>
      have hclosed :
          List.IsChain G.DartAdj (d :: ds ++ [d]) := by
        simpa [hds] using closedWalk_dart_run_closed walk
      simpa [hds] using
        (List.isChain_cons_append_singleton_iff_forall₂).1 hclosed

private theorem exists_next_dart_of_mem_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {d : G.Dart} (hd : d ∈ walk.walk.darts) :
    ∃ sd ∈ walk.walk.darts, G.DartAdj d sd := by
  rcases exists_right_of_forall₂
      (forall₂_dartAdj_tail_append_head_toList_of_closedWalk walk) hd with
    ⟨sd, hsd, hadj⟩
  exact ⟨sd, mem_tail_append_head_toList_subset hsd, hadj⟩

private theorem exists_prev_dart_of_mem_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {d : G.Dart} (hd : d ∈ walk.walk.darts) :
    ∃ p ∈ walk.walk.darts, G.DartAdj p d := by
  have hne : walk.walk.darts ≠ [] := by
    exact List.ne_nil_of_mem hd
  have hd_rot : d ∈ walk.walk.darts.tail ++ walk.walk.darts.head?.toList :=
    mem_tail_append_head_toList_of_mem hne hd
  exact
    exists_left_of_forall₂
      (forall₂_dartAdj_tail_append_head_toList_of_closedWalk walk) hd_rot

private theorem closedWalk_dart_edge_mem_faceBoundary
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {d : G.Dart} (hd : d ∈ walk.walk.darts) :
    (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ emb.faceBoundary f.1 := by
  have hdEdge : d.edge ∈ walk.walk.edges := by
    rw [SimpleGraph.Walk.edges]
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  exact
    (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk.edge_mem_faceBoundary_image_iff
      (emb := emb) (f := f) (e := ⟨d.edge, d.edge_mem⟩)).1
      (by simpa using walk.edge_mem_faceBoundary_image hdEdge)

private theorem edge_ne_of_dartAdj_in_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {p d : G.Dart} (hp : p ∈ walk.walk.darts) (hd : d ∈ walk.walk.darts)
    (hAdj : G.DartAdj p d) :
    p.edge ≠ d.edge := by
  intro hedge
  have hnodup :
      (walk.walk.darts.map fun d : G.Dart => d.edge).Nodup := by
    simpa [SimpleGraph.Walk.edges] using walk.walk_edges_nodup
  have hpdart : p = d :=
    List.inj_on_of_nodup_map hnodup hp hd hedge
  have hloop : p.snd = p.fst := by
    have hadj := hAdj
    simp [hpdart, SimpleGraph.DartAdj] at hadj
  exact p.snd_ne_fst hloop

private theorem next_edge_ne_in_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {f : AmbientFace emb.faces}
    (walk : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {d sd : G.Dart} (hd : d ∈ walk.walk.darts) (hsd : sd ∈ walk.walk.darts)
    (hAdj : G.DartAdj d sd) :
    sd.edge ≠ d.edge :=
  (edge_ne_of_dartAdj_in_closedWalk walk hd hsd hAdj).symm

/-- Honest closed-walk facial boundary data and facewise at-most-one interior edge force the
purified selected-boundary interior-edge endpoint carrier to be empty.  This is stronger than
the successor-cycle obstruction below: it uses only the cyclic dart order already present in the
closed walk for each face. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ := by
  classical
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff emb).1 hv with
      ⟨⟨e, heInterior, hve⟩, havoids⟩
    rcases (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 heInterior with
      ⟨heBiUnion, _heCount⟩
    rcases Finset.mem_biUnion.1 heBiUnion with ⟨f, hf, heFace⟩
    let af : AmbientFace emb.faces := ⟨f, hf⟩
    let walk := closedWalks.faceBoundaryClosedWalk af
    have heWalk : (e : Sym2 V) ∈ walk.walk.edges :=
      walk.faceBoundary_edge_mem_walk heFace
    have heDart : (e : Sym2 V) ∈ walk.walk.darts.map fun d => d.edge := by
      simpa [SimpleGraph.Walk.edges] using heWalk
    rcases List.mem_map.1 heDart with ⟨d, hd, hde⟩
    have hvd : v ∈ d.edge := by
      simpa [hde] using hve
    have hv_cases : v = d.fst ∨ v = d.snd := by
      have hvd' : v ∈ s(d.fst, d.snd) := by
        simpa [SimpleGraph.Dart.edge] using hvd
      exact Sym2.mem_iff.mp hvd'

    have not_interior_of_face_edge_ne (e' : G.edgeSet)
        (he'Face : e' ∈ emb.faceBoundary f) (hne : e' ≠ e) :
        e' ∉ interiorEdgeSupport emb.faceBoundary emb.faces := by
      intro he'Interior
      have heFilter :
          e ∈ (emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨heFace, heInterior⟩
      have he'Filter :
          e' ∈ (emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨he'Face, he'Interior⟩
      have hgt :
          1 <
            ((emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
        rw [Finset.one_lt_card]
        exact ⟨e, heFilter, e', he'Filter, hne.symm⟩
      exact Nat.not_lt_of_ge (h_at_most_one_interior af) hgt

    have selected_of_face_edge_not_interior (e' : G.edgeSet)
        (he'Face : e' ∈ emb.faceBoundary f)
        (hnotInterior : e' ∉ interiorEdgeSupport emb.faceBoundary emb.faces) :
        e' ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
      have he'BiUnion : e' ∈ emb.faces.biUnion emb.faceBoundary :=
        Finset.mem_biUnion.2 ⟨f, hf, he'Face⟩
      refine (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).2 ?_
      refine ⟨he'BiUnion, ?_⟩
      rcases emb.edge_one_or_two_faces e' he'BiUnion with hcount | hcount
      · exact hcount
      · exact False.elim <|
          hnotInterior
            ((mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).2
              ⟨he'BiUnion, hcount⟩)

    rcases hv_cases with hvfst | hvsnd
    · rcases exists_prev_dart_of_mem_closedWalk walk hd with ⟨p, hp, hpAdj⟩
      let ep : G.edgeSet := ⟨p.edge, p.edge_mem⟩
      have hepFace : ep ∈ emb.faceBoundary f :=
        closedWalk_dart_edge_mem_faceBoundary walk hp
      have hpEdgeNe : p.edge ≠ d.edge :=
        edge_ne_of_dartAdj_in_closedWalk walk hp hd hpAdj
      have hepNe : ep ≠ e := by
        intro hepEq
        exact hpEdgeNe <| by
          calc
            p.edge = (e : Sym2 V) := congrArg Subtype.val hepEq
            _ = d.edge := hde.symm
      have hepNotInterior :
          ep ∉ interiorEdgeSupport emb.faceBoundary emb.faces :=
        not_interior_of_face_edge_ne ep hepFace hepNe
      have hepSelected :
          ep ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
        selected_of_face_edge_not_interior ep hepFace hepNotInterior
      have hvp : v ∈ (ep : Sym2 V) := by
        rw [hvfst]
        have htarget : p.snd = d.fst := by
          simpa [SimpleGraph.DartAdj] using hpAdj
        rw [← htarget]
        simpa [ep, SimpleGraph.Dart.edge] using Sym2.mem_mk_right p.fst p.snd
      exfalso
      exact (havoids ep hepSelected) hvp
    · rcases exists_next_dart_of_mem_closedWalk walk hd with ⟨sd, hsd, hAdj⟩
      let es : G.edgeSet := ⟨sd.edge, sd.edge_mem⟩
      have hesFace : es ∈ emb.faceBoundary f :=
        closedWalk_dart_edge_mem_faceBoundary walk hsd
      have hsdEdgeNe : sd.edge ≠ d.edge :=
        next_edge_ne_in_closedWalk walk hd hsd hAdj
      have hesNe : es ≠ e := by
        intro hesEq
        exact hsdEdgeNe <| by
          calc
            sd.edge = (e : Sym2 V) := congrArg Subtype.val hesEq
            _ = d.edge := hde.symm
      have hesNotInterior :
          es ∉ interiorEdgeSupport emb.faceBoundary emb.faces :=
        not_interior_of_face_edge_ne es hesFace hesNe
      have hesSelected :
          es ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
        selected_of_face_edge_not_interior es hesFace hesNotInterior
      have hvs : v ∈ (es : Sym2 V) := by
        rw [hvsnd]
        have hstart : d.snd = sd.fst := by
          simpa [SimpleGraph.DartAdj] using hAdj
        rw [hstart]
        simpa [es, SimpleGraph.Dart.edge] using Sym2.mem_mk_left sd.fst sd.snd
      exfalso
      exact (havoids es hesSelected) hvs
  · intro hv
    simp at hv

/-- Consequently, an honest closed-walk source cannot coexist with facewise at-most-one interior
edge and a nonempty purified interior-edge endpoint carrier on the same embedding. -/
theorem not_exists_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨closedWalks, h_at_most_one_interior, hnonempty⟩
  have hempty :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb closedWalks h_at_most_one_interior
  rw [hempty] at hnonempty
  rcases hnonempty with ⟨v, hv⟩
  simp at hv

/-- The closed-walk annulus source version of the same contradiction.  Boundary reachability and
selected-arc contiguity are irrelevant to the obstruction; the honest cyclic facial walks and
the facewise at-most-one condition already force the purified carrier empty. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨source, h_at_most_one_interior, hnonempty⟩
  exact
    not_exists_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source.closedWalks, h_at_most_one_interior, hnonempty⟩

/-- Necessary local shape of any honest closed-walk source with a surviving purified carrier:
some face boundary must contain two distinct interior edges.  This is the constructive
contrapositive of the empty-carrier theorem above, and rules out searching for a nonempty
honest-source endpoint inside the facewise at-most-one branch. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  classical
  by_contra hnone
  have h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
    intro f
    apply Nat.le_of_not_gt
    intro hgt
    have hgt' :
        1 <
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card := hgt
    rw [Finset.one_lt_card] at hgt'
    rcases hgt' with ⟨e₁, he₁, e₂, he₂, hne⟩
    rcases Finset.mem_filter.1 he₁ with ⟨he₁Face, he₁Interior⟩
    rcases Finset.mem_filter.1 he₂ with ⟨he₂Face, he₂Interior⟩
    exact hnone ⟨f, e₁, he₁Face, he₁Interior, e₂, he₂Face, he₂Interior, hne⟩
  have hempty :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb closedWalks h_at_most_one_interior
  rw [hempty] at hCarrier
  rcases hCarrier with ⟨v, hv⟩
  simp at hv

/-- Route-facing form of the preceding necessary condition.  An honest closed-walk annulus
source together with the live endpoint witness `HasUnblockedInteriorEndpoint` must already have a
face carrying two distinct interior edges. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Graph-level form: no embedding can carry an honest closed-walk annulus source, facewise
at-most-one interior edge, and a nonempty purified interior-edge endpoint carrier at once. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨emb, source, h_at_most_one_interior, hnonempty⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, h_at_most_one_interior, hnonempty⟩

/-- Successor-cycle facial boundary data and facewise at-most-one interior edge force the purified
selected-boundary interior-edge endpoint carrier to be empty.  Thus the nonempty-carrier
hypothesis in the non-vacuous theorem-4.9 synthesis wrappers cannot coexist with this local
at-most-one route unless the source assumptions are changed. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ := by
  classical
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff emb).1 hv with
      ⟨⟨e, heInterior, hve⟩, havoids⟩
    rcases (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 heInterior with
      ⟨heBiUnion, _heCount⟩
    rcases Finset.mem_biUnion.1 heBiUnion with ⟨f, hf, heFace⟩
    let af : AmbientFace emb.faces := ⟨f, hf⟩
    let cycle := dartCycles.faceBoundaryDartSuccessorCycle af
    have heDart : (e : Sym2 V) ∈ cycle.darts.map fun d => d.edge :=
      cycle.hface_sub e heFace
    rcases List.mem_map.1 heDart with ⟨d, hd, hde⟩
    have hvd : v ∈ d.edge := by
      simpa [hde] using hve
    have hv_cases : v = d.fst ∨ v = d.snd := by
      have hvd' : v ∈ s(d.fst, d.snd) := by
        simpa [SimpleGraph.Dart.edge] using hvd
      exact Sym2.mem_iff.mp hvd'

    have not_interior_of_face_edge_ne (e' : G.edgeSet)
        (he'Face : e' ∈ emb.faceBoundary f) (hne : e' ≠ e) :
        e' ∉ interiorEdgeSupport emb.faceBoundary emb.faces := by
      intro he'Interior
      have heFilter :
          e ∈ (emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨heFace, heInterior⟩
      have he'Filter :
          e' ∈ (emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
        Finset.mem_filter.2 ⟨he'Face, he'Interior⟩
      have hgt :
          1 <
            ((emb.faceBoundary f).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
        rw [Finset.one_lt_card]
        exact ⟨e, heFilter, e', he'Filter, hne.symm⟩
      exact Nat.not_lt_of_ge (h_at_most_one_interior af) hgt

    have selected_of_face_edge_not_interior (e' : G.edgeSet)
        (he'Face : e' ∈ emb.faceBoundary f)
        (hnotInterior : e' ∉ interiorEdgeSupport emb.faceBoundary emb.faces) :
        e' ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
      have he'BiUnion : e' ∈ emb.faces.biUnion emb.faceBoundary :=
        Finset.mem_biUnion.2 ⟨f, hf, he'Face⟩
      refine (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).2 ?_
      refine ⟨he'BiUnion, ?_⟩
      rcases emb.edge_one_or_two_faces e' he'BiUnion with hcount | hcount
      · exact hcount
      · exact False.elim <|
          hnotInterior
            ((mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).2
              ⟨he'BiUnion, hcount⟩)

    rcases hv_cases with hvfst | hvsnd
    · have hd_rot :
          d ∈ cycle.darts.tail ++ cycle.darts.head?.toList :=
        mem_tail_append_head_toList_of_mem cycle.hnonempty hd
      rcases exists_predecessor_of_forall₂_successor_order cycle.successor
          cycle.hsuccessor_order hd_rot with
        ⟨p, hp, hpSucc⟩
      let ep : G.edgeSet := ⟨p.edge, p.edge_mem⟩
      have hepFace : ep ∈ emb.faceBoundary f :=
        dart_mem_faceBoundary_of_mem_successor_cycle cycle hp
      have hpEdgeNe : p.edge ≠ d.edge :=
        edge_ne_of_successor_eq_in_successor_cycle cycle hp hd hpSucc
      have hepNe : ep ≠ e := by
        intro hepEq
        exact hpEdgeNe <| by
          calc
            p.edge = (e : Sym2 V) := congrArg Subtype.val hepEq
            _ = d.edge := hde.symm
      have hepNotInterior :
          ep ∉ interiorEdgeSupport emb.faceBoundary emb.faces :=
        not_interior_of_face_edge_ne ep hepFace hepNe
      have hepSelected :
          ep ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
        selected_of_face_edge_not_interior ep hepFace hepNotInterior
      have hvp : v ∈ (ep : Sym2 V) := by
        rw [hvfst]
        have htarget : p.snd = d.fst := by
          have hadj := cycle.hsuccessor_adj p hp
          simpa [SimpleGraph.DartAdj, hpSucc] using hadj
        rw [← htarget]
        simpa [ep, SimpleGraph.Dart.edge] using Sym2.mem_mk_right p.fst p.snd
      exfalso
      exact (havoids ep hepSelected) hvp
    · let sd : G.Dart := cycle.successor d
      let es : G.edgeSet := ⟨sd.edge, sd.edge_mem⟩
      have hsdMem : sd ∈ cycle.darts := by
        simpa [sd] using successor_mem_darts_of_mem_successor_cycle cycle hd
      have hesFace : es ∈ emb.faceBoundary f :=
        dart_mem_faceBoundary_of_mem_successor_cycle cycle hsdMem
      have hsdEdgeNe : sd.edge ≠ d.edge := by
        simpa [sd] using successor_edge_ne_in_successor_cycle cycle hd
      have hesNe : es ≠ e := by
        intro hesEq
        exact hsdEdgeNe <| by
          calc
            sd.edge = (e : Sym2 V) := congrArg Subtype.val hesEq
            _ = d.edge := hde.symm
      have hesNotInterior :
          es ∉ interiorEdgeSupport emb.faceBoundary emb.faces :=
        not_interior_of_face_edge_ne es hesFace hesNe
      have hesSelected :
          es ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
        selected_of_face_edge_not_interior es hesFace hesNotInterior
      have hvs : v ∈ (es : Sym2 V) := by
        rw [hvsnd]
        have hstart : d.snd = sd.fst := by
          have hadj := cycle.hsuccessor_adj d hd
          simpa [sd, SimpleGraph.DartAdj] using hadj
        rw [hstart]
        simpa [es, sd, SimpleGraph.Dart.edge] using Sym2.mem_mk_left sd.fst sd.snd
      exfalso
      exact (havoids es hesSelected) hvs
  · intro hv
    simp at hv

/-- In particular, the route-facing successor-cycle source shell plus facewise at-most-one is
inconsistent with a nonempty purified interior-edge endpoint carrier. -/
theorem not_exists_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨dartCycles, h_at_most_one_interior, hnonempty⟩
  have hempty :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  rw [hempty] at hnonempty
  rcases hnonempty with ⟨v, hv⟩
  simp at hv

/-- On the honest closed-walk source shell, facewise at-most-one interior edge already rules out
the current local endpoint witness.  So the nonempty-carrier upgrade on this branch is not merely
missing; it is incompatible with the present source shell. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  intro hEndpoint
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty :=
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).1 hEndpoint
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, h_at_most_one_interior, hCarrier⟩

/-- The route-facing successor-cycle source shell plus facewise at-most-one also rules out the
current local endpoint witness, after lowering to the honest closed-walk source surface. -/
theorem
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselected :
      ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselected
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior

/-- Even after adding exact one-collar current-boundary data on the same honest closed-walk
source, the facewise at-most-one branch still cannot carry the current endpoint witness. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) ∧
      HasUnblockedInteriorEndpoint emb := by
  rintro ⟨source, _hcurrent, h_at_most_one_interior, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior hEndpoint

/-- The same exact one-collar current-boundary obstruction holds on the live successor-cycle
source shell as well.  So the exact current-boundary diamond branch already carries witness
assignment and theorem-4.9 synthesis on the fixed embedding, but it cannot be upgraded to the
current endpoint-bearing shell without changing the source or carrier interface. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨boundaryData, dartCycles, hselected, _hcurrent, h_at_most_one_interior, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
      boundaryData dartCycles hselected h_at_most_one_interior hEndpoint

/-- Facewise at-most-one interior edge blocks the current projected nonempty theorem-4.9 endpoint
on any honest closed-walk source shell, because that endpoint already contains a nonempty purified
carrier. -/
theorem not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (C0 : G.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  intro hProjected
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, h_at_most_one_interior, hProjected.nonemptySynthesis.carrier_nonempty⟩

/-- The route-facing successor-cycle facewise-at-most-one shell likewise blocks the current
projected nonempty theorem-4.9 endpoint on the same embedding. -/
theorem
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselected :
      ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (C0 : G.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  intro hProjected
  exact
    not_exists_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨dartCycles, h_at_most_one_interior, hProjected.nonemptySynthesis.carrier_nonempty⟩

/-- Exact one-collar current-boundary data do not rescue the honest closed-walk facewise-at-most-
one branch: the projected nonempty theorem-4.9 endpoint is still impossible on that same
embedding. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) ∧
      ∃ C0 : G.EdgeColoring Color,
        Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rintro ⟨source, _hcurrent, h_at_most_one_interior, C0, hProjected⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior C0 hProjected

/-- The same exact one-collar current-boundary obstruction holds on the live successor-cycle shell
itself.  So the projected nonempty endpoint is false there on structural grounds, not merely
underived. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        ∃ C0 : G.EdgeColoring Color,
          Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rintro ⟨boundaryData, dartCycles, hselected, _hcurrent, h_at_most_one_interior, C0, hProjected⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
      boundaryData dartCycles hselected h_at_most_one_interior C0 hProjected

/-- The stronger honest-source shell used by the direct corrected Definition 4.8 bridges still
cannot carry the current local endpoint witness: the extra fallback-edge and boundary-rest data do
not rescue the branch once facewise at-most-one is present. -/
theorem
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (hboundaryRest :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  let _ := hfallback
  let _ := hboundaryRest
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior

/-- The stronger successor-cycle shell likewise still rules out the current endpoint witness on
the same embedding.  So the extra fallback-edge and boundary-rest data only lower the branch to
the corrected Definition 4.8 algebraic floor; they do not restore the missing carrier witness. -/
theorem
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselected :
      ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (hboundaryRest :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  let _ := hfallback
  let _ := hboundaryRest
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
      boundaryData dartCycles hselected h_at_most_one_interior

/-- Even after adding exact one-collar current-boundary data on the stronger honest source shell,
the endpoint witness is still impossible. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_atMostOneInteriorEdgePerFace_and_hasUnblockedInteriorEndpoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      (∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
        (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) ∧
            (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
              e ∈ emb.faceBoundary f.1 →
                e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) ∧
      HasUnblockedInteriorEndpoint emb := by
  rintro ⟨source, _hcurrent, ⟨fallbackEdge, hfallback, h_at_most_one_interior, hboundaryRest⟩,
    hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback h_at_most_one_interior hboundaryRest hEndpoint

/-- The same exact one-collar endpoint obstruction holds on the stronger successor-cycle shell. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_atMostOneInteriorEdgePerFace_and_hasUnblockedInteriorEndpoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨boundaryData, dartCycles, hselected, _hcurrent,
    ⟨fallbackEdge, hfallback, h_at_most_one_interior, hboundaryRest⟩, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
      boundaryData dartCycles hselected fallbackEdge hfallback h_at_most_one_interior
      hboundaryRest hEndpoint

/-- The stronger honest-source shell also still blocks the projected nonempty theorem-4.9
endpoint, since that endpoint already contains a nonempty purified carrier. -/
theorem
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (hboundaryRest :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let _ := hfallback
  let _ := hboundaryRest
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior C0

/-- The stronger route-facing successor-cycle shell likewise still blocks the projected nonempty
theorem-4.9 endpoint on the same embedding. -/
theorem
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselected :
      ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1)
    (hboundaryRest :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let _ := hfallback
  let _ := hboundaryRest
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
      boundaryData dartCycles hselected h_at_most_one_interior C0

/-- Exact one-collar current-boundary data do not rescue the stronger honest closed-walk shell
either: the projected nonempty theorem-4.9 endpoint is still impossible on that same embedding. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_atMostOneInteriorEdgePerFace_and_theorem49BoundaryRootNonemptyProjectedSynthesis
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      (∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
        (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) ∧
            (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
              e ∈ emb.faceBoundary f.1 →
                e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) ∧
      ∃ C0 : G.EdgeColoring Color,
        Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rintro ⟨source, _hcurrent, ⟨fallbackEdge, hfallback, h_at_most_one_interior, hboundaryRest⟩,
    C0, hProjected⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback h_at_most_one_interior hboundaryRest C0 hProjected

/-- The same exact one-collar projected-endpoint obstruction holds on the stronger
successor-cycle shell itself. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_atMostOneInteriorEdgePerFace_and_theorem49BoundaryRootNonemptyProjectedSynthesis
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) ∧
        ∃ C0 : G.EdgeColoring Color,
          Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rintro ⟨boundaryData, dartCycles, hselected, _hcurrent,
    ⟨fallbackEdge, hfallback, h_at_most_one_interior, hboundaryRest⟩, C0, hProjected⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
      boundaryData dartCycles hselected fallbackEdge hfallback h_at_most_one_interior
      hboundaryRest C0 hProjected

/-- The constructive diamond benchmark already inhabits the exact honest closed-walk one-collar
current-boundary at-most-one shell while reaching witness assignment and full theorem-4.9
synthesis, yet the projected nonempty endpoint still fails on that same embedding. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring diamondWithTriangleGraph C ∧
            Theorem49BoundaryRootSynthesis emb C ∧
            ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hcurrent,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
        diamondWithTriangleTaitEdgeColoring⟩

/-- The constructive diamond benchmark already inhabits the exact successor-cycle one-collar
current-boundary at-most-one shell while reaching witness assignment and full theorem-4.9
synthesis, yet the projected nonempty endpoint still fails on that same embedding. -/
theorem
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)) ∧
        ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring diamondWithTriangleGraph C ∧
            Theorem49BoundaryRootSynthesis emb C ∧
            ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  rcases
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph with
    ⟨emb, boundaryData, dartCycles, hselected, hcurrent, h_at_most_one_interior, hwitness, C, hC,
      hSynth⟩
  exact
    ⟨emb, boundaryData, dartCycles, hselected, hcurrent, h_at_most_one_interior, hwitness, C, hC,
      hSynth,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
        boundaryData dartCycles hselected h_at_most_one_interior C⟩

/-- Fixed-embedding graph-level packaging of the same constructive diamond diagnosis: the explicit
Tait coloring already attains theorem-4.9 synthesis on the diamond embedding, while the very same
exact one-collar successor-cycle facewise-at-most-one shell still carries witness assignment but
fails the current projected nonempty endpoint. -/
theorem
    diamondWithTriangleGraph_explicitTait_fixedEmbedding_oneCollarCurrentBoundary_facewiseAtMostOne_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding diamondWithTriangleTaitEdgeColoring ∧
      ∃ boundaryData :
          PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding,
        ∃ dartCycles :
            PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding,
          (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
            ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
                (· ∈
                  interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
                    diamondWithTriangleEmbedding.faces)).card ≤
              (1 : ℕ)) ∧
          Nonempty
            (PlanarBoundaryAnnulusWitnessAssignment
              (planarBoundaryAnnulusDecomposition_of_boundaryData
                boundaryData.toPlanarBoundaryAnnulusBoundaryData)) ∧
          ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis
              diamondWithTriangleEmbedding diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  refine
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleDartSuccessorCycleGeometry,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      ?_⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
      diamondWithTriangleAnnulusBoundaryReachabilityData
      diamondWithTriangleDartSuccessorCycleGeometry
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      diamondWithTriangle_atMostOneInteriorEdgePerFace
      diamondWithTriangleTaitEdgeColoring

/-- Fixed-embedding honest-source packaging of the same constructive diamond diagnosis: the
explicit Tait coloring already attains theorem-4.9 synthesis on the diamond embedding, while the
same exact one-collar honest closed-walk facewise-at-most-one shell still carries annulus witness
assignment but fails the current projected nonempty endpoint. -/
theorem
    diamondWithTriangleGraph_explicitTait_fixedEmbedding_closedWalkOneCollarCurrentBoundary_facewiseAtMostOne_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding diamondWithTriangleTaitEdgeColoring ∧
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
          ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
              (· ∈
                interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
                  diamondWithTriangleEmbedding.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis
            diamondWithTriangleEmbedding diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  refine
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hcurrent,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      ?_⟩
  exact
    not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      diamondWithTriangleClosedWalkAnnulusBoundarySource
      diamondWithTriangle_atMostOneInteriorEdgePerFace
      diamondWithTriangleTaitEdgeColoring

/-!
### Conclusion: Both derivation routes impossible

Combined with `Theorem49CyclicSourceAtMostOneDerivation`, we have now established
the following route obstructions:

1. Cyclic source ↛ at-most-one
   (file: Theorem49CyclicSourceAtMostOneDerivation)

2. At-most-one + closed-walk cyclic source ↛ nonempty carrier
   (this file)

3. Successor-cycle source + at-most-one → empty purified carrier
   (this file)

Therefore:
- At-most-one is an INDEPENDENT sufficient condition for witness choice
- Nonempty carrier is an INDEPENDENT condition for non-vacuous synthesis
- The successor-cycle at-most-one non-vacuous endpoint is incompatible with the current
  selected-boundary-purified carrier, so that route must change one of these hypotheses

The current route architecture is correct in treating both as input hypotheses.

### Future directions

Rather than attempting to derive these conditions, we should:

1. Characterize CLASSES of graphs where at-most-one holds
   - Wheel-with-inner-triangle benchmark: ✗ at-most-one on the fixed embedding
   - Diamond graphs: ✓ at-most-one
   - Chained diamonds: ✓ at-most-one
   - What is the common pattern?

2. Characterize CLASSES of graphs where nonempty carrier holds
   - Wheel graphs: ✓ nonempty carrier
   - Diamond graphs: ✗ nonempty purified carrier on the current selected-boundary embedding
   - Chained diamonds: ✗ empty carrier
   - What causes the difference?

3. Find STRONGER source conditions that DO imply at-most-one
   - Perhaps requiring ALL non-interior edges to be selected (no ambient edges)?
   - Perhaps restricting the embedding structure in some way?

These calibration questions are interesting for CHARACTERIZATION but do not
advance the DERIVATION agenda. The impossibility results are now established.
-/

end Mettapedia.GraphTheory.FourColor
