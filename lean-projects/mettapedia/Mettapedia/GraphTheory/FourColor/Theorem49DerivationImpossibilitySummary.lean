import Mettapedia.GraphTheory.FourColor.Theorem49CyclicSourceAtMostOneDerivation
import Mettapedia.GraphTheory.FourColor.Theorem49AtMostOneNonemptyCarrierImpossibility
import Mettapedia.GraphTheory.FourColor.Theorem49StrengthenedConditionAtMostOneDerivation
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstructionRegression

/-!
# Theorem 4.9 derivation impossibility: summary

This file summarizes the route impossibility results for the Theorem 4.9 annulus synthesis.

## Background

The current Theorem 4.9 route establishes synthesis via:
1. Cyclic source structure (closed walk annulus boundary source)
2. At-most-one-interior-edge-per-face (ASSUMED as hypothesis)
3. Nonempty selectedBoundaryInteriorEdgeEndpointVertices carrier (ASSUMED as hypothesis)

The question was: can we DERIVE conditions (2) and (3) from condition (1)?

## Results established

### Route impossibility 1: Cyclic source ↛ at-most-one

**File:** `Theorem49CyclicSourceAtMostOneDerivation.lean`

**Result:** The cyclic source structure (including closed walks, selected boundary arc
contiguity, and annulus boundary split) does NOT force each face to have at most one
interior edge.

**Counterexample construction:**
```
Face boundary: [e₁, e₂, e₃, e₄, e₅]
- e₁: selected boundary edge
- e₂: interior edge
- e₃: ambient boundary edge
- e₄: interior edge
- e₅: ambient boundary edge
```

This configuration satisfies:
- Selected edges {e₁} form a contiguous subsequence ✓
- Cyclic source axioms hold ✓
- Face has TWO interior edges {e₂, e₄} (violates at-most-one)

**Conclusion:** At-most-one is an INDEPENDENT sufficient condition, not derivable from
the cyclic source.

### Route impossibility 2: At-most-one ↛ nonempty carrier

**File:** `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`

**Result:** The at-most-one condition, even when combined with the cyclic source structure,
does NOT guarantee that the selectedBoundaryInteriorEdgeEndpointVertices carrier is nonempty.

**Counterexample:** The chained-diamonds-with-triangle graph
- Has a cyclic source: `chainedDiamondsClosedWalkAnnulusBoundarySource`
- Satisfies at-most-one: `chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace`
- Has EMPTY carrier: `selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle`

**Explanation:** The carrier contains vertices that are endpoints of interior edges but
NOT endpoints of selected boundary edges. Even if each face has at most one interior edge,
all interior edge endpoints might also be endpoints of selected boundary edges, making
the "purified" carrier empty.

**Conclusion:** Nonempty carrier is an INDEPENDENT condition for non-vacuous synthesis.

The same file now records a stronger route-facing obstruction.  Honest closed-walk facial data
and facewise at-most-one do not merely fail to force nonempty purified carrier: they already
force the purified carrier to be empty.  The successor-cycle version is a special case of this
closed-walk obstruction, and the diamond-with-triangle model is the smallest current concrete
instance of the route-facing successor-cycle obstruction.  Lean also records the constructive
contrapositive: a closed-walk source with a surviving purified carrier, and in particular an
honest closed-walk annulus source with `HasUnblockedInteriorEndpoint`, must have some face
boundary carrying two distinct interior edges.

## Implications

Both attempted derivation routes are IMPOSSIBLE:

1. Cyclic source ↛ at-most-one
2. At-most-one + cyclic source ↛ nonempty carrier
3. Closed-walk or successor-cycle source + at-most-one → empty purified carrier
4. Closed-walk source + nonempty purified carrier → some face has two distinct
   interior edges

Therefore, the current route architecture is CORRECT in treating:
- At-most-one as an INPUT hypothesis for witness choice
- Nonempty carrier as an ADDITIONAL hypothesis for non-vacuous synthesis

Neither can be eliminated or derived from the upstream conditions.  Moreover, the current
successor-cycle at-most-one branch cannot be made non-vacuous by simply adding the existing
purified-carrier hypothesis; one of the geometry or carrier hypotheses has to change.

## Contrast with calibration work

The calibration sessions established that the known finite models separate the
route hypotheses rather than deriving them from one another:

1. Wheel-with-inner-triangle: Tait colorable with nonempty purified carrier, but
   fails the face-local at-most-one condition.
2. Diamond-with-triangle: Tait colorable and satisfies at-most-one, but its current
   selected-boundary purification has empty carrier.
3. Chained-diamonds: satisfies at-most-one source geometry, but has empty carrier
   and no Tait coloring.

These calibrations CHARACTERIZED the boundary conditions but did not DERIVE them.

## Checked summary contribution

This file packages the current derivation-impossibility results as checked Lean
theorems:

- Constructed counterexamples/proofs showing both routes impossible
- Documented WHY the derivations fail (cyclic vs linear order, face-local vs vertex-global)
- Established that the current route's at-most-one and nonempty-carrier hypotheses
  cannot be eliminated by these two derivations

## Future directions (NOT calibration)

Rather than adding more calibration models, future work should:

1. Investigate STRONGER source conditions that DO imply at-most-one
   - E.g., requiring ALL non-interior edges to be selected (no ambient edges)
   - E.g., restricting the embedding structure (triangulated, simple, etc.)

2. Characterize graph CLASSES where at-most-one holds naturally
   - Outerplanar graphs?
   - Graphs with bounded treewidth?
   - K₄-minor-free graphs?

3. Find ALTERNATIVE routes that avoid the at-most-one condition entirely
   - Different witness choice mechanisms?
   - Relaxed contiguity requirements?

But these are EXTENSION questions, not DERIVATION questions. The derivation impossibility
is now established.

## Status summary

- Checked route impossibility 1: cyclic source does not imply at-most-one
- Checked route impossibility 2: at-most-one plus cyclic source does not imply
  nonempty purified carrier
- Checked route impossibility 3: successor-cycle source plus selected arcs and
  at-most-one cannot coexist with nonempty purified carrier
- Checked structural obstruction: closed-walk facial data plus at-most-one forces
  empty purified carrier
- Checked necessary condition: nonempty honest closed-walk source endpoints require
  a face boundary with two distinct interior edges
- The summary theorem below packages both failed universals without using
  placeholders or diagnostic command probes.

-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49ForcingInteriorEdgeObstruction
open Theorem49ForcingInteriorEdgeObstructionRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

variable {V : Type*} [DecidableEq V]

/-- Master failed-universal theorem: neither source data alone nor source data plus the
face-local at-most-one condition supplies the two missing theorem-4.9 hypotheses.  The third
component is now subsumed by the stronger structural theorem below, but it remains useful as the
route-facing failed universal with boundary reachability and selected arcs. -/
theorem theorem49_derivation_routes_impossible :
    (¬ ∀ (G : SimpleGraph (Fin 8)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
    (¬ ∀ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) ∧
    (¬ ∀ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) := by
  exact
    ⟨not_forall_closedWalkSource_implies_atMostOneInteriorEdgePerFace,
      not_forall_closedWalkSource_and_atMostOneInteriorEdgePerFace_implies_nonempty_carrier,
      not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_implies_nonempty_carrier⟩

/-- Structural closed-walk obstruction: with the current selected-boundary-purified carrier,
honest facial closed walks and facewise at-most-one interior edge per face force the purified
interior-edge endpoint carrier to be empty. -/
theorem theorem49_closed_walk_at_most_one_forces_empty_purified_carrier
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
  selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
    emb closedWalks h_at_most_one_interior

/-- Same obstruction in contradiction form: the closed-walk at-most-one source shell cannot
carry a nonempty purified interior-edge endpoint carrier on the same embedding. -/
theorem theorem49_no_closed_walk_at_most_one_nonempty_purified_carrier
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty :=
  not_exists_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    emb

/-- Route-facing closed-walk annulus-source form of the same contradiction. -/
theorem theorem49_no_closed_walk_annulus_source_at_most_one_nonempty_purified_carrier
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty :=
  not_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    emb

/-- Structural successor-cycle obstruction: with the current selected-boundary-purified carrier,
successor-cycle facial dart data and facewise at-most-one interior edge per face force the
purified interior-edge endpoint carrier to be empty. -/
theorem theorem49_successor_cycle_at_most_one_forces_empty_purified_carrier
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
  selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
    emb dartCycles h_at_most_one_interior

/-- Same obstruction in contradiction form: the successor-cycle at-most-one source shell cannot
carry a nonempty purified interior-edge endpoint carrier on the same embedding. -/
theorem theorem49_no_successor_cycle_at_most_one_nonempty_purified_carrier
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ _dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty :=
  not_exists_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    emb

/-- Concrete witness package behind the failed universals: `Fin 8` shared-interior-pair
source for cyclic-source-not-at-most-one, and `Fin 10` chained-diamonds source for
at-most-one-plus-source-not-nonempty-carrier.  The `Fin 7` diamond-with-triangle witness
shows the same empty-carrier phenomenon on the successor-cycle source shell. -/
theorem theorem49_derivation_counterexamples :
    (∃ (G : SimpleGraph (Fin 8)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ¬ ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
    (∃ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) ∧
    (∃ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
          selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
            ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) := by
  exact
    ⟨route_impossibility_at_most_one_not_derivable_from_cyclic_source,
      at_most_one_and_empty_carrier_independent,
      successor_cycle_at_most_one_and_empty_carrier_independent⟩

/-- Root-distance failed converses isolated by the diamond-with-triangle benchmark.  Repaired
previous-boundary witness geometry does not imply the generic interior-dual root-distance package,
and even adding the honest closed-walk annulus source does not imply the two-sided annulus-root
adjacency-distance package. -/
theorem theorem49_root_distance_failed_converses :
    (¬ ∀ {emb : PlaneEmbeddingWithBoundary
          Theorem49InteriorVerticesEndpointObstruction.diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            (V := Fin 7) (F := emb.Face)
            (G := Theorem49InteriorVerticesEndpointObstruction.diamondWithTriangleGraph)
            emb.faces emb.faceBoundary)) ∧
      (¬ ∀ {emb : PlaneEmbeddingWithBoundary
          Theorem49InteriorVerticesEndpointObstruction.diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) := by
  exact
    ⟨not_forall_interiorDualBoundaryRootAdjDistancePeelData_of_previousBoundaryWitnessGeometry_diamondWithTriangle,
      not_forall_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_diamondWithTriangle⟩

/-- Current checked obstruction matrix for the theorem-4.9 annulus route.  The first two
components are the failed derivations already summarized above.  The third records that even
the route-facing successor-cycle selected-arc package with at-most-one still does not force
nonempty purified carrier.  The fourth records that even the stronger boundary-reachability
plus successor-cycle selected-arc package with boundary component constancy still does not
force at-most-one.  The fifth records the wheel benchmark:
Tait coloring and nonempty purified carrier can coexist with a forcing interior edge, blocking
the current annulus-root and face-layer construction routes on the same embedding. -/
theorem theorem49_route_obstruction_matrix :
    (∃ (G : SimpleGraph (Fin 8)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ¬ ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
    (∃ (G : SimpleGraph (Fin 10)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) ∧
    (¬ ∀ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G),
      ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) ∧
    (¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∀ f : AmbientFace emb.faces, boundaryData.BoundaryComponentConstantOnFace f) →
            ∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
    (∃ (G : SimpleGraph (Fin 7)) (emb : PlaneEmbeddingWithBoundary G)
        (C : G.EdgeColoring Color),
      IsTaitEdgeColoring G C ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
        Nonempty (ForcingInteriorEdgeWitness emb) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact route_impossibility_at_most_one_not_derivable_from_cyclic_source
  · exact at_most_one_and_empty_carrier_independent
  · exact
      not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_implies_nonempty_carrier
  · exact
      not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryComponentConstant_implies_atMostOneInteriorEdgePerFace_sharedInteriorPair
  · exact
      ⟨wheelWithInnerTriangleGraph, wheelWithInnerTriangleEmbedding,
        wheelWithInnerTriangleTaitEdgeColoring,
        wheelWithInnerTriangle_tait_nonempty_carrier_and_forcing_obstruction⟩

end Mettapedia.GraphTheory.FourColor
